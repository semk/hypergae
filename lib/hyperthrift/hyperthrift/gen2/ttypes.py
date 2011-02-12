#
# Autogenerated by Thrift
#
# DO NOT EDIT UNLESS YOU ARE SURE THAT YOU KNOW WHAT YOU ARE DOING
#

from cyclozzo.thrift.Thrift import *
import cyclozzo.hyperthrift.gen.ttypes


from cyclozzo.thrift.transport import TTransport
from cyclozzo.thrift.protocol import TBinaryProtocol, TProtocol
try:
  from cyclozzo.thrift.protocol import fastbinary
except:
  fastbinary = None



class HqlResult:
  """
  Result type of HQL queries

  <dl>
    <dt>results</dt>
    <dd>String results from metadata queries</dd>

    <dt>cells</dt>
    <dd>Resulting table cells of for buffered queries</dd>

    <dt>scanner</dt>
    <dd>Resulting scanner ID for unbuffered queries</dd>

    <dt>mutator</dt>
    <dd>Resulting mutator ID for unflushed modifying queries</dd>
  </dl>

  Attributes:
   - results
   - cells
   - scanner
   - mutator
  """

  thrift_spec = (
    None, # 0
    (1, TType.LIST, 'results', (TType.STRING,None), None, ), # 1
    (2, TType.LIST, 'cells', (TType.STRUCT,(cyclozzo.hyperthrift.gen.ttypes.Cell, cyclozzo.hyperthrift.gen.ttypes.Cell.thrift_spec)), None, ), # 2
    (3, TType.I64, 'scanner', None, None, ), # 3
    (4, TType.I64, 'mutator', None, None, ), # 4
  )

  def __init__(self, results=None, cells=None, scanner=None, mutator=None,):
    self.results = results
    self.cells = cells
    self.scanner = scanner
    self.mutator = mutator

  def read(self, iprot):
    if iprot.__class__ == TBinaryProtocol.TBinaryProtocolAccelerated and isinstance(iprot.trans, TTransport.CReadableTransport) and self.thrift_spec is not None and fastbinary is not None:
      fastbinary.decode_binary(self, iprot.trans, (self.__class__, self.thrift_spec))
      return
    iprot.readStructBegin()
    while True:
      (fname, ftype, fid) = iprot.readFieldBegin()
      if ftype == TType.STOP:
        break
      if fid == 1:
        if ftype == TType.LIST:
          self.results = []
          (_etype3, _size0) = iprot.readListBegin()
          for _i4 in xrange(_size0):
            _elem5 = iprot.readString();
            self.results.append(_elem5)
          iprot.readListEnd()
        else:
          iprot.skip(ftype)
      elif fid == 2:
        if ftype == TType.LIST:
          self.cells = []
          (_etype9, _size6) = iprot.readListBegin()
          for _i10 in xrange(_size6):
            _elem11 = cyclozzo.hyperthrift.gen.ttypes.Cell()
            _elem11.read(iprot)
            self.cells.append(_elem11)
          iprot.readListEnd()
        else:
          iprot.skip(ftype)
      elif fid == 3:
        if ftype == TType.I64:
          self.scanner = iprot.readI64();
        else:
          iprot.skip(ftype)
      elif fid == 4:
        if ftype == TType.I64:
          self.mutator = iprot.readI64();
        else:
          iprot.skip(ftype)
      else:
        iprot.skip(ftype)
      iprot.readFieldEnd()
    iprot.readStructEnd()

  def write(self, oprot):
    if oprot.__class__ == TBinaryProtocol.TBinaryProtocolAccelerated and self.thrift_spec is not None and fastbinary is not None:
      oprot.trans.write(fastbinary.encode_binary(self, (self.__class__, self.thrift_spec)))
      return
    oprot.writeStructBegin('HqlResult')
    if self.results != None:
      oprot.writeFieldBegin('results', TType.LIST, 1)
      oprot.writeListBegin(TType.STRING, len(self.results))
      for iter12 in self.results:
        oprot.writeString(iter12)
      oprot.writeListEnd()
      oprot.writeFieldEnd()
    if self.cells != None:
      oprot.writeFieldBegin('cells', TType.LIST, 2)
      oprot.writeListBegin(TType.STRUCT, len(self.cells))
      for iter13 in self.cells:
        iter13.write(oprot)
      oprot.writeListEnd()
      oprot.writeFieldEnd()
    if self.scanner != None:
      oprot.writeFieldBegin('scanner', TType.I64, 3)
      oprot.writeI64(self.scanner)
      oprot.writeFieldEnd()
    if self.mutator != None:
      oprot.writeFieldBegin('mutator', TType.I64, 4)
      oprot.writeI64(self.mutator)
      oprot.writeFieldEnd()
    oprot.writeFieldStop()
    oprot.writeStructEnd()
    def validate(self):
      return


  def __repr__(self):
    L = ['%s=%r' % (key, value)
      for key, value in self.__dict__.iteritems()]
    return '%s(%s)' % (self.__class__.__name__, ', '.join(L))

  def __eq__(self, other):
    return isinstance(other, self.__class__) and self.__dict__ == other.__dict__

  def __ne__(self, other):
    return not (self == other)

class HqlResult2:
  """
  Same as HqlResult except with cell as array

  Attributes:
   - results
   - cells
   - scanner
   - mutator
  """

  thrift_spec = (
    None, # 0
    (1, TType.LIST, 'results', (TType.STRING,None), None, ), # 1
    (2, TType.LIST, 'cells', (TType.LIST,(TType.STRING,None)), None, ), # 2
    (3, TType.I64, 'scanner', None, None, ), # 3
    (4, TType.I64, 'mutator', None, None, ), # 4
  )

  def __init__(self, results=None, cells=None, scanner=None, mutator=None,):
    self.results = results
    self.cells = cells
    self.scanner = scanner
    self.mutator = mutator

  def read(self, iprot):
    if iprot.__class__ == TBinaryProtocol.TBinaryProtocolAccelerated and isinstance(iprot.trans, TTransport.CReadableTransport) and self.thrift_spec is not None and fastbinary is not None:
      fastbinary.decode_binary(self, iprot.trans, (self.__class__, self.thrift_spec))
      return
    iprot.readStructBegin()
    while True:
      (fname, ftype, fid) = iprot.readFieldBegin()
      if ftype == TType.STOP:
        break
      if fid == 1:
        if ftype == TType.LIST:
          self.results = []
          (_etype17, _size14) = iprot.readListBegin()
          for _i18 in xrange(_size14):
            _elem19 = iprot.readString();
            self.results.append(_elem19)
          iprot.readListEnd()
        else:
          iprot.skip(ftype)
      elif fid == 2:
        if ftype == TType.LIST:
          self.cells = []
          (_etype23, _size20) = iprot.readListBegin()
          for _i24 in xrange(_size20):
            _elem25 = []
            (_etype29, _size26) = iprot.readListBegin()
            for _i30 in xrange(_size26):
              _elem31 = iprot.readString();
              _elem25.append(_elem31)
            iprot.readListEnd()
            self.cells.append(_elem25)
          iprot.readListEnd()
        else:
          iprot.skip(ftype)
      elif fid == 3:
        if ftype == TType.I64:
          self.scanner = iprot.readI64();
        else:
          iprot.skip(ftype)
      elif fid == 4:
        if ftype == TType.I64:
          self.mutator = iprot.readI64();
        else:
          iprot.skip(ftype)
      else:
        iprot.skip(ftype)
      iprot.readFieldEnd()
    iprot.readStructEnd()

  def write(self, oprot):
    if oprot.__class__ == TBinaryProtocol.TBinaryProtocolAccelerated and self.thrift_spec is not None and fastbinary is not None:
      oprot.trans.write(fastbinary.encode_binary(self, (self.__class__, self.thrift_spec)))
      return
    oprot.writeStructBegin('HqlResult2')
    if self.results != None:
      oprot.writeFieldBegin('results', TType.LIST, 1)
      oprot.writeListBegin(TType.STRING, len(self.results))
      for iter32 in self.results:
        oprot.writeString(iter32)
      oprot.writeListEnd()
      oprot.writeFieldEnd()
    if self.cells != None:
      oprot.writeFieldBegin('cells', TType.LIST, 2)
      oprot.writeListBegin(TType.LIST, len(self.cells))
      for iter33 in self.cells:
        oprot.writeListBegin(TType.STRING, len(iter33))
        for iter34 in iter33:
          oprot.writeString(iter34)
        oprot.writeListEnd()
      oprot.writeListEnd()
      oprot.writeFieldEnd()
    if self.scanner != None:
      oprot.writeFieldBegin('scanner', TType.I64, 3)
      oprot.writeI64(self.scanner)
      oprot.writeFieldEnd()
    if self.mutator != None:
      oprot.writeFieldBegin('mutator', TType.I64, 4)
      oprot.writeI64(self.mutator)
      oprot.writeFieldEnd()
    oprot.writeFieldStop()
    oprot.writeStructEnd()
    def validate(self):
      return


  def __repr__(self):
    L = ['%s=%r' % (key, value)
      for key, value in self.__dict__.iteritems()]
    return '%s(%s)' % (self.__class__.__name__, ', '.join(L))

  def __eq__(self, other):
    return isinstance(other, self.__class__) and self.__dict__ == other.__dict__

  def __ne__(self, other):
    return not (self == other)
