#! /usr/bin/env python
#
# Datastore implementation for Hypertable.
#	It should be registered by 
#		apiproxy_stub_map.apiproxy.RegisterStub('datastore', DatastoreStub())
#
# @author: Sreejith K
# Created on 27th March 2010

import logging
import threading
import datetime
import re
import array
import itertools
import uuid

from thriftclient import ThriftClient
from hyperthrift.gen.ttypes import ClientException, Cell, Key, RowInterval, ScanSpec
from google.appengine.api import apiproxy_stub
from google.appengine.api import datastore, datastore_types, datastore_errors, users
from google.appengine.datastore import datastore_pb, entity_pb
from google.appengine.datastore import sortable_pb_encoder
from google.appengine.datastore import datastore_index
from google.appengine.datastore import datastore_stub_util

log = logging.getLogger(__name__)

_MAXIMUM_RESULTS = 1000
_MAX_QUERY_OFFSET = 1000
_MAX_QUERY_COMPONENTS = 100
_BATCH_SIZE = 20
_MAX_ACTIONS_PER_TXN = 5
_CURSOR_CONCAT_STR = '!CURSOR!'


class _Cursor(object):
  """A query cursor.

  Public properties:
    cursor: the integer cursor
    count: the original total number of results
    keys_only: whether the query is keys_only
    app: the app for which this cursor was created

  Class attributes:
    _next_cursor: the next cursor to allocate
    _next_cursor_lock: protects _next_cursor
  """
  _next_cursor = 1
  _next_cursor_lock = threading.Lock()

  def __init__(self, query, results, order_compare_entities):
    """Constructor.

    Args:
      query: the query request proto
      # the query results, in order, such that results[self.offset+1] is
      # the next result
      results: list of datastore.Entity
      order_compare_entities: a __cmp__ function for datastore.Entity that
        follows sort order as specified by the query
    """

    if query.has_compiled_cursor() and query.compiled_cursor().position_list():
      (self.__last_result, inclusive) = self._DecodeCompiledCursor(
          query, query.compiled_cursor())
      start_cursor_position = _Cursor._GetCursorOffset(results,
                                                       self.__last_result,
                                                       inclusive,
                                                       order_compare_entities)
    else:
      self.__last_result = None
      start_cursor_position = 0

    if query.has_end_compiled_cursor():
      (end_cursor_entity, inclusive) = self._DecodeCompiledCursor(
          query, query.end_compiled_cursor())
      end_cursor_position = _Cursor._GetCursorOffset(results,
                                                     end_cursor_entity,
                                                     inclusive,
                                                     order_compare_entities)
    else:
      end_cursor_position = len(results)

    results = results[start_cursor_position:end_cursor_position]

    if query.has_limit():
      limit = query.limit()
      if query.offset():
        limit += query.offset()
      if limit > 0 and limit < len(results):
        results = results[:limit]

    self.__results = results
    self.__query = query
    self.__offset = 0

    self.app = query.app()
    self.keys_only = query.keys_only()
    self.count = len(self.__results)
    self.cursor = self._AcquireCursorID()

  def _AcquireCursorID(self):
    """Acquires the next cursor id in a thread safe manner.
    """
    self._next_cursor_lock.acquire()
    try:
      cursor_id = _Cursor._next_cursor
      _Cursor._next_cursor += 1
    finally:
      self._next_cursor_lock.release()
    return cursor_id

  @staticmethod
  def _GetCursorOffset(results, cursor_entity, inclusive, compare):
    """Converts a cursor entity into a offset into the result set even if the
    cursor_entity no longer exists.

    Args:
      cursor_entity: the decoded datastore.Entity from the compiled query
      inclusive: boolean that specifies if to offset past the cursor_entity
      compare: a function that takes two datastore.Entity and compares them
    Returns:
      the integer offset
    """
    lo = 0
    hi = len(results)
    if inclusive:
      while lo < hi:
        mid = (lo + hi) // 2
        if compare(results[mid], cursor_entity) < 0:
          lo = mid + 1
        else:
          hi = mid
    else:
      while lo < hi:
        mid = (lo + hi) // 2
        if compare(cursor_entity, results[mid]) < 0:
          hi = mid
        else:
          lo = mid + 1
    return lo

  def _ValidateQuery(self, query, query_info):
    """Ensure that the given query matches the query_info.

    Args:
      query: datastore_pb.Query instance we are chacking
      query_info: datastore_pb.Query instance we want to match

    Raises BadRequestError on failure.
    """
    error_msg = 'Cursor does not match query: %s'
    exc = datastore_errors.BadRequestError
    if query_info.filter_list() != query.filter_list():
      raise exc(error_msg % 'filters do not match')
    if query_info.order_list() != query.order_list():
      raise exc(error_msg % 'orders do not match')

    for attr in ('ancestor', 'kind', 'name_space', 'search_query'):
      query_info_has_attr = getattr(query_info, 'has_%s' % attr)
      query_info_attr = getattr(query_info, attr)
      query_has_attr = getattr(query, 'has_%s' % attr)
      query_attr = getattr(query, attr)
      if query_info_has_attr():
        if not query_has_attr() or query_info_attr() != query_attr():
          raise exc(error_msg % ('%s does not match' % attr))
      elif query_has_attr():
        raise exc(error_msg % ('%s does not match' % attr))

  def _MinimalQueryInfo(self, query):
    """Extract the minimal set of information for query matching.

    Args:
      query: datastore_pb.Query instance from which to extract info.

    Returns:
      datastore_pb.Query instance suitable for matching against when
      validating cursors.
    """
    query_info = datastore_pb.Query()
    query_info.set_app(query.app())

    for filter in query.filter_list():
      query_info.filter_list().append(filter)
    for order in query.order_list():
      query_info.order_list().append(order)

    if query.has_ancestor():
      query_info.mutable_ancestor().CopyFrom(query.ancestor())

    for attr in ('kind', 'name_space', 'search_query'):
      query_has_attr = getattr(query, 'has_%s' % attr)
      query_attr = getattr(query, attr)
      query_info_set_attr = getattr(query_info, 'set_%s' % attr)
      if query_has_attr():
        query_info_set_attr(query_attr())

    return query_info

  def _MinimalEntityInfo(self, entity_proto, query):
    """Extract the minimal set of information that preserves entity order.

    Args:
      entity_proto: datastore_pb.EntityProto instance from which to extract
      information
      query: datastore_pb.Query instance for which ordering must be preserved.

    Returns:
      datastore_pb.EntityProto instance suitable for matching against a list of
      results when finding cursor positions.
    """
    entity_info = datastore_pb.EntityProto();
    order_names = [o.property() for o in query.order_list()]
    entity_info.mutable_key().MergeFrom(entity_proto.key())
    entity_info.mutable_entity_group().MergeFrom(entity_proto.entity_group())
    for prop in entity_proto.property_list():
      if prop.name() in order_names:
        entity_info.add_property().MergeFrom(prop)
    return entity_info;

  def _DecodeCompiledCursor(self, query, compiled_cursor):
    """Converts a compiled_cursor into a cursor_entity.

    Returns:
      (cursor_entity, inclusive): a datastore.Entity and if it should be
      included in the result set.
    """
    assert len(compiled_cursor.position_list()) == 1

    position = compiled_cursor.position(0)
    entity_pb = datastore_pb.EntityProto()
    (query_info_encoded, entity_encoded) = position.start_key().split(
        _CURSOR_CONCAT_STR, 1)
    query_info_pb = datastore_pb.Query()
    query_info_pb.ParseFromString(query_info_encoded)
    self._ValidateQuery(query, query_info_pb)

    entity_pb.ParseFromString(entity_encoded)
    return (datastore.Entity._FromPb(entity_pb, True),
            position.start_inclusive())

  def _EncodeCompiledCursor(self, query, compiled_cursor):
    """Converts the current state of the cursor into a compiled_cursor

    Args:
      query: the datastore_pb.Query this cursor is related to
      compiled_cursor: an empty datstore_pb.CompiledCursor
    """
    if self.__last_result is not None:
      position = compiled_cursor.add_position()
      query_info = self._MinimalQueryInfo(query)
      entity_info = self._MinimalEntityInfo(self.__last_result.ToPb(), query)
      start_key = _CURSOR_CONCAT_STR.join((
          query_info.Encode(),
          entity_info.Encode()))
      position.set_start_key(str(start_key))
      position.set_start_inclusive(False)

  def PopulateQueryResult(self, result, count, offset, compile=False):
    """Populates a QueryResult with this cursor and the given number of results.

    Args:
      result: datastore_pb.QueryResult
      count: integer of how many results to return
      offset: integer of how many results to skip
      compile: boolean, whether we are compiling this query
    """
    offset = min(offset, self.count - self.__offset)
    limited_offset = min(offset, _MAX_QUERY_OFFSET)
    if limited_offset:
      self.__offset += limited_offset
      result.set_skipped_results(limited_offset)

    if offset == limited_offset and count:
      if count > _MAXIMUM_RESULTS:
        count = _MAXIMUM_RESULTS
      results = self.__results[self.__offset:self.__offset + count]
      count = len(results)
      self.__offset += count
      result.result_list().extend(r._ToPb() for r in results)

    if self.__offset:
      self.__last_result = self.__results[self.__offset - 1]

    result.mutable_cursor().set_app(self.app)
    result.mutable_cursor().set_cursor(self.cursor)
    result.set_keys_only(self.keys_only)
    result.set_more_results(self.__offset < self.count)
    if compile:
      self._EncodeCompiledCursor(
          self.__query, result.mutable_compiled_cursor())


class HypertableStub(apiproxy_stub.APIProxyStub):

	_PROPERTY_TYPE_TAGS = {
		datastore_types.Blob: entity_pb.PropertyValue.kstringValue,
		bool: entity_pb.PropertyValue.kbooleanValue,
		datastore_types.Category: entity_pb.PropertyValue.kstringValue,
		datetime.datetime: entity_pb.PropertyValue.kint64Value,
		datastore_types.Email: entity_pb.PropertyValue.kstringValue,
		float: entity_pb.PropertyValue.kdoubleValue,
		datastore_types.GeoPt: entity_pb.PropertyValue.kPointValueGroup,
		datastore_types.IM: entity_pb.PropertyValue.kstringValue,
		int: entity_pb.PropertyValue.kint64Value,
		datastore_types.Key: entity_pb.PropertyValue.kReferenceValueGroup,
		datastore_types.Link: entity_pb.PropertyValue.kstringValue,
		long: entity_pb.PropertyValue.kint64Value,
		datastore_types.PhoneNumber: entity_pb.PropertyValue.kstringValue,
		datastore_types.PostalAddress: entity_pb.PropertyValue.kstringValue,
		datastore_types.Rating: entity_pb.PropertyValue.kint64Value,
		str: entity_pb.PropertyValue.kstringValue,
		datastore_types.Text: entity_pb.PropertyValue.kstringValue,
		type(None): 0,
		unicode: entity_pb.PropertyValue.kstringValue,
		users.User: entity_pb.PropertyValue.kUserValueGroup,
   	 }


	def __init__(self, app_id, schema='/etc/cyclozzo/default.schema.xml',
				thrift_address='127.0.0.1',
				thrift_port='38080', 
				service_name='datastore_v3', 
				trusted=False):
		"""
		Initialize this stub with the service name.
		"""
		self.__app_id = app_id
		self.__schema = schema
		self.__thrift_address = thrift_address
		self.__thrift_port = thrift_port
		self.__trusted = trusted
		self.__queries = {}

		super(HypertableStub, self).__init__(service_name)

	def _GetThriftClient(self):
		"""Get a new Thrift connection"""
		return ThriftClient(self.__thrift_address, self.__thrift_port)

	def _Create_Obj_Datastore(self, client, kind):
		table_name = str('%s_%s' % (self.__app_id, kind))
		try:
			if not self.__app_id or len(self.__app_id) == 0:
				raise app.NotSignedInError('App id is empty or invalid')
			table = client.get_table_id(table_name)
		except ClientException, e:
			cfg = open(self.__schema, 'r')
			schema = ''
			for line in cfg.readlines():
				schema += line
			client.create_table(table_name, schema)
			log.debug('creating hypertable %s' % table_name)
		
	def _AppIdNamespaceKindForKey(self, key):
		""" Get (app, kind) tuple from given key.
	
		The (app, kind) tuple is used as an index into several internal
		dictionaries, e.g. __entities.
	
		Args:
			key: entity_pb.Reference
	
		Returns:
			Tuple (app, kind), both are unicode strings.
		"""
		last_path = key.path().element_list()[-1]
		return (datastore_types.EncodeAppIdNamespace(key.app(), key.name_space()),
				last_path.type())

	@staticmethod
	def __EncodeIndexPB(pb):
		if isinstance(pb, entity_pb.PropertyValue) and pb.has_uservalue():
			userval = entity_pb.PropertyValue()
			userval.mutable_uservalue().set_email(pb.uservalue().email())
			userval.mutable_uservalue().set_auth_domain(pb.uservalue().auth_domain())
			userval.mutable_uservalue().set_gaiaid(0)
			pb = userval
		encoder = sortable_pb_encoder.Encoder()
		pb.Output(encoder)
		return buffer(encoder.buffer().tostring())

	@staticmethod
	def __GetEntityKind(key):
		if isinstance(key, entity_pb.EntityProto):
			key = key.key()
		return key.path().element_list()[-1].type()

	def __ValidateAppId(self, app_id):
		"""Verify that this is the stub for app_id.
	
		Args:
			app_id: An application ID.
	
		Raises:
			datastore_errors.BadRequestError: if this is not the stub for app_id.
		"""
		assert app_id
		if not self.__trusted and app_id != self.__app_id:
			raise datastore_errors.BadRequestError(
					'app %s cannot access app %s\'s data' % (self.__app_id, app_id))

	def __ValidateKey(self, key):
		"""Validate this key.

		Args:
			key: entity_pb.Reference

		Raises:
			datastore_errors.BadRequestError: if the key is invalid
		"""
		assert isinstance(key, entity_pb.Reference)

		self.__ValidateAppId(key.app())

		for elem in key.path().element_list():
			if elem.has_id() == elem.has_name():
				raise datastore_errors.BadRequestError(
					'each key path element should have id or name but not both: %r'
					% key)

	def __GenerateNewKey(self, kind):
		return datastore_types.Key.from_path( kind, str(uuid.uuid4()).replace('-', '')[:10] )

	def _Dynamic_Put(self, put_request, put_response):
		client = self._GetThriftClient()
		entities = put_request.entity_list()
		log.debug('writing %s entities' % len(entities))
		kind_cells_dict = {}

		for entity in entities:
			self.__ValidateKey(entity.key())
			
			for prop in itertools.chain(entity.property_list(),
									entity.raw_property_list()):
				datastore_stub_util.FillUser(prop)

			assert entity.has_key()
			assert entity.key().path().element_size() > 0
			
			last_path = entity.key().path().element_list()[-1]
			if last_path.id() == 0 and not last_path.has_name():
				#id_ = self.__AllocateIds(conn, self._GetTablePrefix(entity.key()), 1)
				#last_path.set_id(id_)
				
				assert entity.entity_group().element_size() == 0
				group = entity.mutable_entity_group()
				root = entity.key().path().element(0)
				group.add_element().CopyFrom(root)
			else:
				assert (entity.has_entity_group() and
					entity.entity_group().element_size() > 0)
			
			kind = self.__GetEntityKind(entity)
			# create table for this kind if not created already.
			self._Create_Obj_Datastore(client, kind)
			
			if kind_cells_dict.has_key(kind):
				kind_cells_dict[kind].append(entity)
			else:
				kind_cells_dict[kind] = [entity]

		put_keys = []
		for kind in kind_cells_dict.keys():
			table_name = str('%s_%s' % (self.__app_id, kind))
			mutator = client.open_mutator(table_name, 0, 0)

			entities = kind_cells_dict[kind]
			for entity in entities:
				try:
					log.debug('using provided key')
					key = datastore_types.Key._FromPb(entity.key())
					# encode the key
					encoded_key = str(key)
				except datastore_errors.BadKeyError:
					log.debug('generating a new key')
					# generate the key for this entity
					key = self.__GenerateNewKey(kind)
					# encode the key
					encoded_key = str(key)
				log.debug('encoded key: %r' %encoded_key)
				meta_cell1 = Cell(
									Key(
										row = encoded_key,
										column_family = 'meta', 
										column_qualifier = 'kind', 
										flag = 255),
									kind)
				meta_cell2 = Cell(
									Key(
										row = encoded_key,
										column_family = 'meta', 
										column_qualifier = 'app', 
										flag = 255),
									self.__app_id)
				entity_cell = Cell(
									Key(
										row = encoded_key,
										column_family = 'entity', 
										column_qualifier = 'proto', 
										flag = 255),
									str(buffer(entity.Encode())))
				client.set_cell(mutator, meta_cell1)
				client.set_cell(mutator, meta_cell2)
				client.set_cell(mutator, entity_cell)
				put_keys.append(key._ToPb())
			client.close_mutator(mutator, True);
		client.close()
		log.debug('done.')
		put_response.key_list().extend(put_keys)

	
	def _Dynamic_Delete(self, delete_request, delete_response):
		client = self._GetThriftClient()
		keys = [datastore_types.Key._FromPb(key) for key in delete_request.key_list()]
		log.debug('deleting %s entities' % len(keys))
		kind_keys_dict = {}
		for key in keys:
			if kind_keys_dict.has_key(key.kind()):
				kind_keys_dict[key.kind()].append(key)
			else:
				kind_keys_dict[key.kind()] = [key]

		for kind in kind_keys_dict:
			table_name = str('%s_%s' % (self.__app_id, kind))
			mutator = client.open_mutator(table_name, 0, 0)
			this_kind_keys = [str(key) for key in kind_keys_dict[kind]]
			for this_key in this_kind_keys:
				log.debug('deleting cells with key: %s' %this_key)
				this_key_cells = Cell(
									Key(
										row = this_key,
										flag = 0),
									)
				client.set_cells(mutator, [this_key_cells])
			client.close_mutator(mutator, True);
		client.close()

	def _Dynamic_Drop(self, drop_request, drop_response):
		client = self._GetThriftClient()
		kind = drop_request.kind
		table_name = str('%s_%s' % (self.__app_id, kind))
		client.drop_table(table_name, 1)
		client.close()
	
	def _Dynamic_Get(self, get_request, get_response):
		client = self._GetThriftClient()
		keys = get_request.key_list()
		kind_keys_dict = {}
		
		for key in keys:
			kind = self._AppIdNamespaceKindForKey(key)[1]
			if kind_keys_dict.has_key(kind):
				kind_keys_dict[kind].append(key)
			else:
				kind_keys_dict[kind] = [key]
		
		entities = []
		for kind in kind_keys_dict:
			table_name = str('%s_%s' % (self.__app_id, kind))
			for key in kind_keys_dict[kind]:
				total_cells = []
				key_pb = key
				key = datastore_types.Key._FromPb(key)
				row_spec = RowInterval(start_row = str(key),
									start_inclusive = True,
									end_row = str(key),
									end_inclusive = True)
				scanner_id = client.open_scanner(table_name,
												ScanSpec(columns = ['meta', 'entity'],
														row_intervals = [row_spec],
														row_limit = 0,
														revs = 1),
												True);
				while True:
					cells = client.next_cells(scanner_id)
					if len(cells) > 0:
						total_cells += cells
					else:
						break
				client.close_scanner(scanner_id)

				for cell in total_cells:
					if cell.key.column_family == 'entity' and cell.key.column_qualifier == 'proto':
						entity_proto = entity_pb.EntityProto(str(cell.value))
						entity_proto.mutable_key().CopyFrom(key_pb)
						group = get_response.add_entity()
						group.mutable_entity().CopyFrom(entity_proto)
		client.close()

	def _Dynamic_RunQuery(self, query, query_result):
		client = self._GetThriftClient()
		kind = query.kind()
		keys_only = query.keys_only()
		filters = query.filter_list()
		orders = query.order_list()
		offset = query.offset()
		limit = query.limit()
		namespace = query.name_space()
		#predicate = query.predicate()
		
		table_name = str('%s_%s' % (self.__app_id, kind))
		
		if filters or orders:
			row_limit = 0
		else:
			row_limit = offset + limit
		
		scanner_id = client.open_scanner(table_name,
										ScanSpec(columns = ['meta', 'entity'],
												row_limit = row_limit,
												revs = 1,
												keys_only = keys_only),
										True);
		total_cells = []
		while True:
			cells = client.next_cells(scanner_id)
			if len(cells) > 0:
				total_cells += cells
			else:
				break
		client.close_scanner(scanner_id)
		
		# make a cell-key dictionary
		key_cell_dict = {}
		for cell in total_cells:
			if key_cell_dict.has_key(cell.key.row):
				key_cell_dict[cell.key.row].append(cell)
			else:
				key_cell_dict[cell.key.row] = [cell]
				
		pb_entities = []
		for key in key_cell_dict:
			key_obj = datastore_types.Key(encoded=key)
			key_pb = key_obj._ToPb()
			for cell in key_cell_dict[key]:
				if cell.key.column_family == 'entity' and cell.key.column_qualifier == 'proto':
					entity_proto = entity_pb.EntityProto(str(cell.value))
					entity_proto.mutable_key().CopyFrom(key_pb)
					pb_entities.append(entity_proto)
		
		results = map(lambda entity: datastore.Entity.FromPb(entity), pb_entities)
	
		query.set_app(self.__app_id)
		datastore_types.SetNamespace(query, namespace)
		encoded = datastore_types.EncodeAppIdNamespace(self.__app_id, namespace)
	
		operators = {datastore_pb.Query_Filter.LESS_THAN:			 '<',
					 datastore_pb.Query_Filter.LESS_THAN_OR_EQUAL:	'<=',
					 datastore_pb.Query_Filter.GREATER_THAN:			'>',
					 datastore_pb.Query_Filter.GREATER_THAN_OR_EQUAL: '>=',
					 datastore_pb.Query_Filter.EQUAL:				 '==',
					 }
	
		def has_prop_indexed(entity, prop):
			"""Returns True if prop is in the entity and is indexed."""
			if prop in datastore_types._SPECIAL_PROPERTIES:
				return True
			elif prop in entity.unindexed_properties():
				return False
	
			values = entity.get(prop, [])
			if not isinstance(values, (tuple, list)):
				values = [values]
	
			for value in values:
				if type(value) not in datastore_types._RAW_PROPERTY_TYPES:
					return True
			return False
	
		for filt in filters:
			assert filt.op() != datastore_pb.Query_Filter.IN
	
			prop = filt.property(0).name().decode('utf-8')
			op = operators[filt.op()]
	
			filter_val_list = [datastore_types.FromPropertyPb(filter_prop)
							 for filter_prop in filt.property_list()]
	
			def passes_filter(entity):
				"""Returns True if the entity passes the filter, False otherwise.
		
				The filter being evaluated is filt, the current filter that we're on
				in the list of filters in the query.
				"""
				log.debug('filter check for entity: %r' %entity)
				if not has_prop_indexed(entity, prop):
					return False
		
				try:
					entity_vals = datastore._GetPropertyValue(entity, prop)
				except KeyError:
					entity_vals = []
		
				if not isinstance(entity_vals, list):
					entity_vals = [entity_vals]
		
				for fixed_entity_val in entity_vals:
					for filter_val in filter_val_list:
						fixed_entity_type = self._PROPERTY_TYPE_TAGS.get(
																		fixed_entity_val.__class__)
						filter_type = self._PROPERTY_TYPE_TAGS.get(filter_val.__class__)
						if fixed_entity_type == filter_type:
							comp = u'%r %s %r' % (fixed_entity_val, op, filter_val)
						elif op != '==':
							comp = '%r %s %r' % (fixed_entity_type, op, filter_type)
						else:
							continue
		
						logging.log(logging.DEBUG - 1,
								'Evaling filter expression "%s"', comp)
		
						try:
							ret = eval(comp)
							if ret and ret != NotImplementedError:
								return True
						except TypeError:
							pass
		
				return False
	
			results = filter(passes_filter, results)
		log.debug('entity list after filter operation: %r' %results)
	
		for order in orders:
			prop = order.property().decode('utf-8')
			results = [entity for entity in results if has_prop_indexed(entity, prop)]
	
		def order_compare_entities(a, b):
			""" Return a negative, zero or positive number depending on whether
			entity a is considered smaller than, equal to, or larger than b,
			according to the query's orderings. """
			cmped = 0
			for o in orders:
				prop = o.property().decode('utf-8')
		
				reverse = (o.direction() is datastore_pb.Query_Order.DESCENDING)
		
				a_val = datastore._GetPropertyValue(a, prop)
				if isinstance(a_val, list):
					a_val = sorted(a_val, order_compare_properties, reverse=reverse)[0]
		
				b_val = datastore._GetPropertyValue(b, prop)
				if isinstance(b_val, list):
					b_val = sorted(b_val, order_compare_properties, reverse=reverse)[0]
		
				cmped = order_compare_properties(a_val, b_val)
		
				if o.direction() is datastore_pb.Query_Order.DESCENDING:
					cmped = -cmped
	
				if cmped != 0:
					return cmped
	
			if cmped == 0:
				return cmp(a.key(), b.key())
	
		def order_compare_properties(x, y):
			"""Return a negative, zero or positive number depending on whether
			property value x is considered smaller than, equal to, or larger than
			property value y. If x and y are different types, they're compared based
			on the type ordering used in the real datastore, which is based on the
			tag numbers in the PropertyValue PB.
			"""
			if isinstance(x, datetime.datetime):
				x = datastore_types.DatetimeToTimestamp(x)
			if isinstance(y, datetime.datetime):
				y = datastore_types.DatetimeToTimestamp(y)
	
			x_type = self._PROPERTY_TYPE_TAGS.get(x.__class__)
			y_type = self._PROPERTY_TYPE_TAGS.get(y.__class__)
	
			if x_type == y_type:
				try:
					return cmp(x, y)
				except TypeError:
					return 0
			else:
				return cmp(x_type, y_type)
	
		results.sort(order_compare_entities)

		cursor = _Cursor(query, results, order_compare_entities)
		self.__queries[cursor.cursor] = cursor
	
		if query.has_count():
			count = query.count()
		elif query.has_limit():
			count = query.limit()
		else:
			count = _BATCH_SIZE
	
		cursor.PopulateQueryResult(query_result, count,
									 query.offset(), compile=query.compile())
	
		if query.compile():
			compiled_query = query_result.mutable_compiled_query()
			compiled_query.set_keys_only(query.keys_only())
			compiled_query.mutable_primaryscan().set_index_name(query.Encode())
	
	def _Dynamic_Next(self, next_request, query_result):
		self.__ValidateAppId(next_request.cursor().app())
	
		cursor_handle = next_request.cursor().cursor()
	
		try:
			cursor = self.__queries[cursor_handle]
		except KeyError:
			raise apiproxy_errors.ApplicationError(
				datastore_pb.Error.BAD_REQUEST, 'Cursor %d not found' % cursor_handle)
	
		assert cursor.app == next_request.cursor().app()
	
		count = _BATCH_SIZE
		if next_request.has_count():
			count = next_request.count()
		cursor.PopulateQueryResult(query_result,
									 count, next_request.offset(),
									 next_request.compile())
	
	def _Dynamic_Count(self, query, integer64proto):
		query_result = datastore_pb.QueryResult()
		self._Dynamic_RunQuery(query, query_result)
		cursor = query_result.cursor().cursor()
		integer64proto.set_value(min(self.__queries[cursor].count, _MAXIMUM_RESULTS))
		del self.__queries[cursor]
