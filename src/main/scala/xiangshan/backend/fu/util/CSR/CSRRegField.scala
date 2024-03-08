package xiangshan.backend.fu.util.CSR

import chisel3._
import chisel3.experimental.SourceInfo
import chisel3.experimental.BundleLiterals._
import chisel3.internal.firrtl.Width
import chisel3.util.{Cat, MixedVec, MuxCase, RegEnable, ValidIO}
import com.fasterxml.jackson.databind.exc.MismatchedInputException
import top.{ArgParser, Generator}
import xiangshan.backend.fu.util.CSRDef

import scala.collection.{SeqMap, immutable}

abstract class CSRField(val msb: Int, val lsb: Int) extends Bundle {
  val fieldWidth = msb - lsb + 1

  override def toPrintable: Printable = s"[$msb, $lsb]"
}

abstract class CSRRealField(
  override val msb: Int,
  override val lsb: Int,
  val wfn: (UInt, UInt, Seq[CSRField]) => UInt
) extends CSRField(msb, lsb) {
  var v = UInt(fieldWidth.W)
}

case class CSRRegField(
  override val msb: Int,
  override val lsb: Int,
  override val wfn: (UInt, UInt, Seq[CSRField]) => UInt
) extends CSRRealField(
  msb, lsb, wfn,
) {
}

case class CSRWireField(
  override val msb: Int,
  override val lsb: Int,
) extends CSRRealField(
  msb, lsb, null,
) {
}

case class CSRPadField(
  override val msb: Int,
  override val lsb: Int,
) extends CSRRealField(msb, lsb,  wfn = null) {
}

case class CSRRefField(
  refField: CSRField
) extends CSRField(refField.msb, refField.lsb)

class CSRModule[T <: CSRBundle](
  val modName: String,
  val gen: T
) extends Module {

  override def desiredName: String = "Module" + modName

  val io = IO(new CSRModuleIO)

  val regs = Reg(gen)
  println(regs.elements)
  regs.elements.foreach { case (name: String, field: CSREnumType) =>
    println(s"$name width: ${field.getWidth}, ${io.w.bits.elements(name).getWidth}")
    when (io.w.valid) {
      field := field.factory(field.wfn(io.w.bits.elements(name).asUInt, field.asUInt, Seq()))
    }
  }

  val rdata = Wire(gen)
  rdata :|= regs

  io.r.data := rdata.asUInt

  class CSRModuleIO extends Bundle {
    val w = Flipped(ValidIO(gen))
    val r = Output(new Bundle {
      val data = UInt()
    })
  }
}

class CSREnumType(
  val msb: Int,
  val lsb: Int
)(
  val wfn: CSRFuncTrait#CSRWfnType,
  val rfn: CSRFuncTrait#CSRRfnType,
  val implicitWfn: CSRFuncTrait#CSRImplicitWfnType,
)(
  override val factory: ChiselEnum
) extends EnumType(factory) with CSRFuncTrait {
  override def toString: String = {
    s"CSREnumType[$msb, $lsb]"
  }

  if (factory.all.isEmpty) {
    factory.asInstanceOf[CSREnum].addMaxValue
  }
}

trait CSRFuncTrait {
  type CSRWfnType = (UInt, UInt, Seq[Data]) => UInt

  def wNoFilter: CSRWfnType =
    (newV: UInt, oldV: UInt, _: Seq[Data]) => newV

  def wNoEffectWhen(keepCond: UInt => Bool): CSRWfnType =
    (newV: UInt, oldV: UInt, _: Seq[Data]) => {
      Mux(keepCond(newV), oldV, newV)
    }

  def wNoEffect: CSRWfnType =
    (_: UInt, oldV: UInt, _: Seq[Data]) => { oldV }

  type CSRRfnType = (UInt, Seq[Data]) => UInt

  def rNoFilter: CSRRfnType =
    (oriV: UInt, _: Seq[Data]) => oriV

  def rWithFilter(rFilter: (UInt, Seq[Data]) => UInt): CSRRfnType =
    (oriV: UInt, seq: Seq[Data]) => rFilter(oriV, seq)

  type CSRImplicitWfnType = (UInt, Seq[Data]) => UInt
}

class CSREnum(msb: Int, lsb: Int) extends ChiselEnum with CSRFuncTrait {
  def this(bit: Int) = this(bit, bit)

  def apply(wfn: CSRWfnType, rfn: CSRRfnType, impWfn: CSRImplicitWfnType): CSREnumType =
    new CSREnumType(msb, lsb)(wfn, rfn, impWfn)(this)

  /**
   * A trick to expand the width of Enum to (msb - lsb + 1)
   */
  def addMaxValue: Unit = {
    Value(((BigInt(1) << (msb - lsb + 1)) - 1).U)
  }
}

class CSRWARLField(msb: Int, lsb: Int) extends CSREnum(msb, lsb) {
  def this(bit: Int) = this(bit, bit)

  def apply(wfn: CSRWfnType, rfn: CSRRfnType = rNoFilter): CSREnumType = super.apply(wfn = wfn, rfn = rfn, null)
}

class CSRROField(msb: Int, lsb: Int) extends CSREnum(msb, lsb) {
  def this(bit: Int) = this(bit, bit)

  def apply(rfn: CSRRfnType): CSREnumType = super.apply(wfn = wNoEffect, rfn = rfn, null)
}

trait CSRContextStatusDef { this: ChiselEnum =>
  val Off = Value(0.U)
  val Initial = Value(1.U)
  val Clean = Value(2.U)
  val Dirty = Value(3.U)
}

abstract class CSRBundle(len: Int = 64) extends Bundle {
  override def do_asUInt(implicit sourceInfo: SourceInfo): UInt = {
    val fields = this.getFields
    var paddedFields: Seq[Data] = Seq()
    var lsb = len

    for (field <- fields) {
      if (field.msb + 1 != lsb)
        paddedFields :+= 0.U((lsb - field.msb - 1).W)
      paddedFields :+= field
      lsb = field.lsb
    }

    if (fields.last.lsb > 0) {
      paddedFields :+= 0.U(fields.last.lsb.W)
    }

    Cat(paddedFields.map(x => x.asUInt))
  }

  def := (that: UInt): Unit = {
    val fields = this.getFields

    for (field <- fields) {
      field := field.factory.apply(that(field.msb, field.lsb))
    }
  }

  /**
   * filtered read connection
   *
   * CSRBundle will be filtered by CSRFields' read filter function.
   */
  def :|= [T <: CSRBundle](that: T): Unit = {
    if (this.getClass != that.getClass) {
      throw MonoConnectException(s"Type miss match! (sink :|= source) " +
        s"sink type: ${this.getClass}, " +
        s"source type: ${that.getClass}")
    }

    for ((sink: CSREnumType, source: CSREnumType)  <- this.getFields.zip(that.getFields)) {
      println(sink, sink.rfn)
      sink := sink.factory.apply(sink.rfn(source.asUInt, Seq()))
    }
  }

  def getFields = this.getElements.map(_.asInstanceOf[CSREnumType])
}

class NewCSR extends Module with CSRDef with CSRFuncTrait {
  val io = IO(new Bundle {
    val w = Flipped(ValidIO(new Bundle {
      val addr = UInt(12.W)
      val data = UInt(64.W)
    }))
    val trap = Flipped(ValidIO(new Bundle {
      val toPRVM = PrivMode()
      val toV = VirtMode()
    }))
    val tret = Flipped(ValidIO(new Bundle {
      val toPRVM = PrivMode()
      val toV = VirtMode()
    }))
  })

  val addr = io.w.bits.addr
  val data = io.w.bits.data
  val wen = io.w.valid

  val PRVM = RegInit(PrivMode.M)
  val V = RegInit(VirtMode.Off)

  val trap = io.trap.valid
  val trapToPRVM = io.trap.bits.toPRVM
  val trapToV = io.trap.bits.toV
  val trapToM = trapToPRVM === PrivMode.M
  val trapToHS = trapToPRVM === PrivMode.S && trapToV === VirtMode.Off
  val trapToHU = trapToPRVM === PrivMode.U && trapToV === VirtMode.Off
  val trapToVS = trapToPRVM === PrivMode.S && trapToV === VirtMode.On
  val trapToVU = trapToPRVM === PrivMode.U && trapToV === VirtMode.On

  val tret = io.tret.valid
  val tretPRVM = io.tret.bits.toPRVM
  val tretV = io.tret.bits.toV
  val isSret = tret && tretPRVM === PrivMode.S
  val isMret = tret && tretPRVM === PrivMode.M

  val mstatus = Module(new CSRModule("Mstatus", new CSRBundle {
    val SIE  = new CSRWARLField(1)(wNoFilter)
    val MIE  = new CSRWARLField(3)(wNoFilter)
    val SPIE = new CSRWARLField(5)(wNoFilter)
    val MPIE = new CSRWARLField(7)(wNoFilter)
    val SPP  = new CSRWARLField(8)(wNoFilter)
    val VS   = (new CSRWARLField(10,  9) with CSRContextStatusDef)(wNoFilter)
    val MPP  = new CSRWARLField(12, 11)(wNoFilter)
    val FS   = (new CSRWARLField(14, 13) with CSRContextStatusDef)(wNoFilter)
    val MPRV = new CSRWARLField(17)(wNoFilter)
    val SUM  = new CSRWARLField(18)(wNoFilter)
    val MXR  = new CSRWARLField(19)(wNoFilter)
    val TVM  = new CSRWARLField(20)(wNoFilter)
    val TW   = new CSRWARLField(21)(wNoFilter)
    val TSR  = new CSRWARLField(22)(wNoFilter)
    val GVA  = new CSRWARLField(38)(wNoFilter)
    val MPV  = new CSRWARLField(39)(wNoFilter)
    val SD   = new CSRROField(63)(
      (_, _) =>
        FS === FS.factory.asInstanceOf[CSRContextStatusDef].Dirty ||
        VS === VS.factory.asInstanceOf[CSRContextStatusDef].Dirty
    )
  }))

  val mtvec = Module(new CSRModule("Mtvec", new CSRBundle {
    val mode = new CSRWARLField( 1, 0)(wNoEffectWhen(MtvecModeEncode.isReserved))
    val addr = new CSRWARLField(63, 2)(wNoFilter)
  }))

  val hip = Module(new CSRModule("Hip", new CSRBundle {
    val VSSIP = new CSRWARLField( 2)(wNoFilter)
    val VSTIP = new CSRWARLField( 6)(wNoEffect)
    val VSEIP = new CSRWARLField(10)(wNoEffect)
    val SGEIP = new CSRWARLField(12)(wNoEffect)
  }))

  val CSRMap = SeqMap(
    0x300 -> mstatus,
    0x305 -> mtvec,
    0x644 -> hip,
  )

  for ((id, mod) <- CSRMap) {
    mod.io.w.valid := wen && addr === id.U
    mod.io.w.bits := data
    dontTouch(mod.io)
  }
}

object NewCSRMain extends App with CSRDef {
  val (config, firrtlOpts, firtoolOpts) = ArgParser.parse(
    args :+ "--disable-always-basic-diff" :+ "--dump-fir" :+ "--fpga-platform")
  def wNoFilter = (newV: UInt, oldV: UInt, _: Seq[CSRField]) => newV
  def wWithFilter(notChangeF: UInt => Bool): (UInt, UInt, Seq[CSRField]) => UInt =
    (newV: UInt, oldV: UInt, _: Seq[CSRField]) => { Mux(notChangeF(newV), oldV, newV) }

  Generator.execute(
    firrtlOpts :+ "--full-stacktrace" :+ "--target-dir" :+ "backend",
    new NewCSR,
    Array()
  )
  println("done")
}
