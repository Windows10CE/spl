/****************************************************************************************************
 *
 * File: MIPS.scala
 * Generation of MIPS code from IR code
 *
 ****************************************************************************************************/

package edu.uta.spl

/** representation of a MIPS register */
case class Register ( reg: String ) {
    override def toString: String = s"$$$reg"
}


/** a pool of available registers */
class RegisterPool {

  val all_registers
        = List( "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9",
                "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7" )

  var available_registers: List[Register] = all_registers.map(Register)

  /** is register reg temporary? */
  def is_temporary ( reg: Register ): Boolean =
    reg match {
      case Register(n) => all_registers.contains(n)
    }

  /** return the next available temporary register */
  def get (): Register =
    available_registers match {
      case reg::rs
        => available_registers = rs
           reg
      case _ => throw new Error("*** Run out of registers")
    }

  /** recycle (put back into the register pool) the register reg (if is temporary) */
  def recycle ( reg: Register ) {
    if (available_registers.contains(reg))
       throw new Error("*** Register has already been recycled: "+reg)
    if (is_temporary(reg))
       available_registers = reg::available_registers
  }

  /** return the list of all temporary registers currently in use */
  def used (): List[Register] = {
    for ( reg <- all_registers if !available_registers.contains(Register(reg)) )
        yield Register(reg)
  }
}


abstract class MipsGenerator {
  def clear ()
  def emit ( e: IRstmt )
  def initialCode ()
}


class Mips extends MipsGenerator {
 
  /** emit a MIPS label */
  def mips_label ( s: String ) {
    SPL.out.println(s + ":")
  }

  /** emit MIPS code with no operands */
  def mips ( op: String ) {
    SPL.out.println("        " + op)
  }

  /** emit MIPS code with operands */
  def mips ( op: String, args: Any* ) {
    SPL.out.print("        " + op)
    for ( i <- op.length to 10)
        SPL.out.print(" ")
    SPL.out.print(args(0))
    for (extraArg <- args.tail)
      SPL.out.print(s", $extraArg")
    SPL.out.println()
  }

  /** a pool of temporary registers */
  var rpool = new RegisterPool

  /** clear the register pool */
  def clear {
    rpool = new RegisterPool
  }

  var name_counter = 0

  /** generate a new  label name */
  def new_label (): String = {
    name_counter += 1
    "L_" + name_counter
  }

  def emit_call(name: String, staticLink: IRexp, args: List[IRexp]) = {
    val used_regs = rpool.used()
    val size = (used_regs.length + args.length) * 4
    /* allocate space for used temporary registers */
    if (size > 0)
      mips("subu", "$sp", "$sp", size)
    /* push the used temporary registers */
    var i = size
    for (r <- used_regs) {
      mips("sw", r, s"$i($$sp)")
      i -= 4
    }
    /* push arguments */
    i = args.length * 4
    for (a <- args) {
      val reg = emit(a)
      mips("sw", reg, s"$i($$sp)")
      rpool.recycle(reg)
      i -= 4
    }
    /* set $v0 to be the static link */
    val sreg = emit(staticLink)
    mips("move", "$v0", sreg)
    rpool.recycle(sreg)
    mips("jal", name)
    i = size
    /* pop the used temporary registers */
    for (r <- used_regs) {
      mips("lw", r, s"$i($$sp)")
      i -= 4
    }
    /* deallocate stack from args and used temporary registers */
    if (size > 0)
      mips("addu", "$sp", "$sp", size)
  }

  /** generate MIPS code from the IR expression e and return the register that will hold the result */
  def emit ( e: IRexp ): Register = {
    e match {
      case Mem(Binop("PLUS",Reg(r),IntValue(n))) =>
        val reg = rpool.get()
        mips("lw", reg, s"$n($$$r)")
        reg
      case Call(f,sl,args) =>
        emit_call(f, sl, args)
        val res = rpool.get()
        mips("move", res, "$a0")
        /* You shouldn't just return $a0 */
        res

      /* PUT YOUR CODE HERE */
      case Reg(r) => Register(r)

      case IntValue(v) =>
        val reg = rpool.get()
        mips("li", reg, v)
        reg

      case FloatValue(v) =>
        val reg = rpool.get()
        mips("li", reg, v)
        reg

      case StringValue(v) =>
        mips(".data")
        mips(".align", "2")
        val label = new_label()
        mips_label(label)
        mips(".asciiz", '"' + v + '"')
        mips(".text")
        val reg = rpool.get()
        mips("la", reg, label)
        reg

      case Binop(opcode@("AND" | "OR"), left, right) =>
        val endLabel = new_label()
        val leftReg = emit(left)
        mips("beq", leftReg, if (opcode == "AND") 0 else 1, endLabel)
        val rightReg = emit(right)
        mips("move", leftReg, rightReg)
        rpool.recycle(rightReg)
        mips_label(endLabel)
        leftReg
      case Binop(op, left, right) =>
        val leftReg = emit(left)
        val rightReg = emit(right)
        val opCode = op match {
          case "PLUS" => "addu"
          case "MINUS" => "subu"
          case "TIMES" => "mul"
          case "DIV" => "div"
          case "MOD" => "rem"
          case "EQ" => "seq"
          case "NEQ" => "sne"
          case "GT" => "sgt"
          case "LT" => "slt"
          case "GEQ" => "sge"
          case "LEQ" => "sle"
        }
        val resultReg = if (rpool.is_temporary(leftReg)) {
          mips(opCode, leftReg, leftReg, rightReg)
          leftReg
        } else {
          val resultReg = rpool.get()
          mips(opCode, resultReg, leftReg, rightReg)
          resultReg
        }
        rpool.recycle(rightReg)
        resultReg

      case Unop(op, operand) =>
        val operandReg = emit(operand)
        op match {
          case "MINUS" => mips("neg", operandReg, operandReg)
          case "NOT" => mips("seq", operandReg, operandReg, 0)
        }
        operandReg

      case Mem(Binop("PLUS", baseAddr, IntValue(offset))) =>
        val reg = rpool.get()
        val addrReg = emit(baseAddr)
        mips("lw", reg, s"$offset($addrReg)")
        if (rpool.is_temporary(addrReg)) rpool.recycle(addrReg)
        reg
        
      case Mem(addr) =>
        val reg = rpool.get()
        val addrReg = emit(addr)
        mips("lw", reg, s"($addrReg)")
        if (rpool.is_temporary(addrReg)) rpool.recycle(addrReg)
        reg

      case Allocate(size) =>
        val sizeReg = emit(size)
        val temp = rpool.get()
        mips("li", temp, 4)
        mips("mul", sizeReg, sizeReg, temp)
        mips("move", temp, "$gp")
        mips("addu", "$gp", "$gp", sizeReg)
        rpool.recycle(sizeReg)
        temp

      case _ => throw new Error("*** Unknown IR: "+e)
    }
  }

  /** generate MIPS code from the IR statement e */
  def emit ( e: IRstmt ) {
    e match {
      case Move(Mem(Binop("PLUS",Reg(r),IntValue(n))),u) =>
        val src = emit(u)
        mips("sw", src, s"$n($$$r)")
        rpool.recycle(src)

      /* PUT YOUR CODE HERE */
      case Label(name) => mips_label(name)

      // moves to register
      case Move(Reg(dest), Mem(Binop("PLUS", baseAddr, IntValue(offset)))) =>
        mips("lw", Register(dest), s"$offset(${emit(baseAddr)})")

      case Move(Reg(dest), Mem(addr)) =>
        mips("lw", Register(dest), s"(${emit(addr)})")

      case Move(Reg(dest), IntValue(value)) =>
        mips("li", Register(dest), value)
      
      case Move(Reg(dest), src) =>
        mips("move", Register(dest), emit(src))
        
      // stores to memory
      case Move(Mem(Binop("PLUS", baseAddr, IntValue(offset))), src) =>
        val baseReg = emit(baseAddr)
        val value = emit(src)
        mips("sw", value, s"$offset($baseReg)")
        
      case Move(Mem(dest), src) =>
        val destReg = emit(dest)
        val srcReg = emit(src)
        mips("sw", srcReg, s"($destReg)")

      case Return() => mips("jr", "$ra")

      case SystemCall("WRITE_STRING", StringValue("\\n")) =>
        mips("li", "$v0", 4)
        mips("la", "$a0", "ENDL_")
        mips("syscall")
      case SystemCall(name, operand) =>
        val callNum = name match {
          case "READ_INT" => 5
          case "READ_FLOAT" => 6
          case "WRITE_INT" => 1
          case "WRITE_FLOAT" => 2
          case "WRITE_STRING" => 4
        }
        var destAddr: Register = null
        callNum match {
          case 5 | 6 =>
            destAddr = emit(operand.asInstanceOf[Mem].address)
            mips("li", "$v0", callNum)
            mips("syscall")
            mips("sw", if (callNum == 5) "$v0" else "$f0", s"($destAddr)")
          case 1 | 2 | 4 =>
            destAddr = emit(operand)
            mips("move", if (callNum != 2) "$a0" else "$f12", destAddr)
            mips("li", "$v0", callNum)
            mips("syscall")
        }
        if (rpool.is_temporary(destAddr)) rpool.recycle(destAddr)

      case Jump(label) => mips("j", label)

      case CJump(cond, label) =>
        val condReg = emit(cond)
        mips("beq", condReg, 1, label)
        rpool.recycle(condReg)

      case CallP(f,sl,args) => emit_call(f, sl, args)

      case _ => throw new Error("*** Unknown IR "+e)
    }
  }

  /** generate initial MIPS code from the program */
  def initialCode () {
    mips(".globl","main")
    mips(".data")
    mips_label("ENDL_")
    mips(".asciiz","\"\\n\"")
    mips(".text")
  }
}
