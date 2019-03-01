package bus.simplebus

import chisel3._
import chisel3.util._

import bus.axi4._

class SimpleBus2AXI4Converter[T <: AXI4Lite](_type: T = new AXI4) extends Module {
  val io = IO(new Bundle {
    val in = Flipped(new SimpleBus)
    val out = _type
  })

  val mem = io.in
  val axi = io.out

  val ar = axi.ar.bits
  val aw = axi.aw.bits
  val w  = axi.w.bits
  val r  = axi.r.bits
  val b  = axi.b.bits

  ar.addr  := mem.req.bits.addr
  ar.prot  := AXI4Parameters.PROT_PRIVILEDGED
  w.data := mem.req.bits.wdata
  w.strb := mem.req.bits.wmask

  io.out match {
    case axi4: AXI4 =>
      axi4.ar.bits.id    := 0.U
      axi4.ar.bits.len   := 0.U  // single beat
      axi4.ar.bits.size  := mem.req.bits.size
      axi4.ar.bits.burst := AXI4Parameters.BURST_INCR
      axi4.ar.bits.lock  := false.B
      axi4.ar.bits.cache := 0.U
      axi4.ar.bits.qos   := 0.U
      axi4.ar.bits.user  := 0.U
      axi4.w.bits.last := true.B
    case axi4lite: AXI4Lite =>
  }

  aw := ar
  mem.resp.bits.rdata := r.data

  val awAck = RegInit(false.B)
  val wAck = RegInit(false.B)

  val wen = RegEnable(mem.req.bits.wen, mem.req.fire())
  val wSend = (axi.aw.fire() && axi.w.fire()) || (awAck && wAck)
  when (wSend) {
    awAck := false.B
    wAck := false.B
  }
  .elsewhen (axi.aw.fire()) { awAck := true.B }
  .elsewhen (axi. w.fire()) {  wAck := true.B }

  axi.ar.valid := mem.isRead()
  axi.aw.valid := mem.isWrite() && !awAck
  axi.w .valid := mem.isWrite() && !wAck
  mem.req.ready  := Mux(mem.req.bits.wen, wSend, axi.ar.ready)

  axi.r.ready  := mem.resp.ready
  axi.b.ready  := mem.resp.ready
  mem.resp.valid  := Mux(wen, axi.b.valid, axi.r.valid)
}
