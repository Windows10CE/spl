package edu.uta.spl

abstract class TypeChecker {
  var trace_typecheck = false

  /** symbol table to store SPL declarations */
  var st = new SymbolTable

  def expandType ( tp: Type ): Type
  def typecheck ( e: Expr ): Type
  def typecheck ( e: Lvalue ): Type
  def typecheck ( e: Stmt, expected_type: Type )
  def typecheck ( e: Definition )
  def typecheck ( e: Program )
}


class TypeCheck extends TypeChecker {

  /** typechecking error */
  def error ( msg: String ): Type = {
    System.err.println("*** Typechecking Error: "+msg)
    System.err.println("*** Symbol Table: "+st)
    System.exit(1)
    null
  }

  /** if tp is a named type, expand it */
  def expandType ( tp: Type ): Type =
    tp match {
      case NamedType(nm)
        => st.lookup(nm) match {
          case Some(TypeDeclaration(t))
              => expandType(t)
          case _ => error("Undeclared type: "+tp)
        }
      case _ => tp
  }

  /** returns true if the types tp1 and tp2 are equal under structural equivalence */
  def typeEquivalence ( tp1: Type, tp2: Type ): Boolean =
    if (tp1 == tp2 || tp1.isInstanceOf[AnyType] || tp2.isInstanceOf[AnyType])
      true
    else expandType(tp1) match {
      case ArrayType(t1)
        => expandType(tp2) match {
              case ArrayType(t2)
                => typeEquivalence(t1,t2)
              case _ => false
           }
      case RecordType(fs1)
        => expandType(tp2) match {
              case RecordType(fs2)
                => fs1.length == fs2.length &&
                   (fs1 zip fs2).map{ case (Bind(v1,t1),Bind(v2,t2))
                                        => v1==v2 && typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case TupleType(ts1)
        => expandType(tp2) match {
              case TupleType(ts2)
                => ts1.length == ts2.length &&
                   (ts1 zip ts2).map{ case (t1,t2) => typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case _
        => tp2 match {
             case NamedType(n) => typeEquivalence(tp1,expandType(tp2))
             case _ => false
           }
    }

  /* tracing level */
  var level: Int = -1

  /** trace typechecking */
  def trace[T] ( e: Any, result: => T ): T = {
    if (trace_typecheck) {
       level += 1
       println(" "*(3*level)+"** "+e)
    }
    val res = result
    if (trace_typecheck) {
       print(" "*(3*level))
       if (e.isInstanceOf[Stmt] || e.isInstanceOf[Definition])
          println("->")
       else println("-> "+res)
       level -= 1
    }
    res
  }

  /** typecheck an expression AST */
  def typecheck ( e: Expr ): Type =
    trace(e,e match {
      case BinOpExp(op,l,r)
        => val ltp = typecheck(l)
           val rtp = typecheck(r)
           if (!typeEquivalence(ltp,rtp))
              error("Incompatible types in binary operation: "+e)
           else if (op.equals("and") || op.equals("or"))
                   if (typeEquivalence(ltp,BooleanType()))
                      ltp
                   else error("AND/OR operation can only be applied to booleans: "+e)
           else if (op.equals("eq") || op.equals("neq"))
                   BooleanType()
           else if (!typeEquivalence(ltp,IntType()) && !typeEquivalence(ltp,FloatType()))
                   error("Binary arithmetic operations can only be applied to integer or real numbers: "+e)
           else if (op.equals("gt") || op.equals("lt") || op.equals("geq") || op.equals("leq"))
                   BooleanType()
           else ltp

      /* PUT YOUR CODE HERE */
      case IntConst(_) => IntType()
      case FloatConst(_) => FloatType()
      case StringConst(_) => StringType()
      case BooleanConst(_) => BooleanType()
      case NullExp() => AnyType()
      
      case LvalExp(lv) => typecheck(lv)

      case UnOpExp(op, operand) =>
        val operandType = typecheck(operand)
        op match {
          case "minus" if typeEquivalence(operandType, IntType()) || typeEquivalence(operandType, FloatType()) => operandType
          case "not" if typeEquivalence(operandType, BooleanType()) => operandType
          case _ => error(s"$op is not supported on type $operandType")
        }

      case CallExp(name, args) =>
        st.lookup(name) match {
          case Some(FuncDeclaration(outT, params, _, _, _)) =>
            val argTypes = args.map(typecheck)
            val paramTypes = params.map(_.value)
            if (argTypes.length != paramTypes.length) error(s"expected ${paramTypes.length} arguments, got ${argTypes.length}")
            else argTypes.zip(paramTypes).find { case (left, right) => !typeEquivalence(left, right) } match {
              case Some((argT, paramT)) => error(s"expected type $paramT, got type $argT")
              case None => outT
            }
          case Some(_) => error(s"$name is not a function")
          case None => error(s"$name does not exist in this scope")
        }

      case RecordExp(fields) => RecordType(fields.map(bind => Bind(bind.name, typecheck(bind.value))))

      case ArrayExp(elements) => ArrayType(
        elements.map(typecheck).fold(AnyType()) {
          case (AnyType(), t) => t
          case (t, AnyType()) => t
          case (t1, t2) =>
            if (typeEquivalence(t1, t2)) t1
            else error(s"types $t1 and $t2 are different, and therefore an array cannot be created with both")
        }
      )

      case ArrayGen(length, value) =>
        if (!typeEquivalence(IntType(), typecheck(length))) {
          error(s"$length should have type int, but does not")
        }
        ArrayType(typecheck(value))

      case TupleExp(exprs) => TupleType(exprs.map(typecheck))
    } )

  /** typecheck an Lvalue AST */
  def typecheck ( e: Lvalue ): Type =
    trace(e,e match {
      case Var(name)
        => st.lookup(name) match {
              case Some(VarDeclaration(t,_,_)) => t
              case Some(_) => error(name+" is not a variable")
              case None => error("Undefined variable: "+name)
        }

      /* PUT YOUR CODE HERE */
      case ArrayDeref(array, index) => 
        if (!typeEquivalence(IntType(), typecheck(index))) {
          error(s"$index should have type int, but does not")
        }
        expandType(typecheck(array)) match {
          case ArrayType(inner) => inner
          case t => error(s"$t is not an array type")
        }

      case RecordDeref(record, attr) =>
        expandType(typecheck(record)) match {
          case t @ RecordType(fields) =>
            fields.find(_.name == attr) match {
              case Some(f) => f.value
              case None => error(s"$t does not contain the field $attr")
            }
          case t => error(s"$t is not a record type")
        }

      case TupleDeref(tuple, index) =>
        expandType(typecheck(tuple)) match {
          case tt @ TupleType(inners) => inners.lift(index) match {
            case Some(t) => t
            case None => error(s"Tuple type $tt only has ${inners.length} elements, and do cannot be indexed at $index")
          }
          case t => error(s"Expected tuple type, found $t")
        }
    } )

  /** typecheck a statement AST using the expected type of the return value from the current function */
  def typecheck ( e: Stmt, expected_type: Type ) {
    trace(e,e match {
      case AssignSt(d,s)
        => if (!typeEquivalence(typecheck(d),typecheck(s)))
              error("Incompatible types in assignment: "+e)

      /* PUT YOUR CODE HERE */
      case CallSt(name, args) =>
        st.lookup(name) match {
          case Some(FuncDeclaration(_, params, _, _, _)) =>
            if (args.length != params.length) {
              error(s"supplied ${args.length} args, expected ${params.length}")
            }
            else args.map(typecheck).zip(params).find { case (arg, param) => !typeEquivalence(arg, param.value) } match {
              case Some((argT, paramT)) => error(s"Argument type $argT does not match parameter type $paramT")
              case None => ()
            }
          case Some(_) => error(s"$name is not a function")
          case None => error(s"$name is not the name of any binding in scope")
        }

      case ReadSt(args) =>
        args.map(arg => expandType(typecheck(arg))).find(arg => !arg.isInstanceOf[IntType] && !arg.isInstanceOf[FloatType]) match {
          case Some(failedType) => error(s"All read arguments must be int or float, found $failedType")
          case None => ()
        }

      case PrintSt(args) =>
        args.map(arg => expandType(typecheck(arg))).find(arg => !arg.isInstanceOf[IntType] && !arg.isInstanceOf[FloatType] && !arg.isInstanceOf[BooleanType] && !arg.isInstanceOf[StringType]) match {
          case Some(t) => error(s"All print arguments must be int, float, boolean, or string, found $t")
          case None => ()
        }

      case IfSt(cond, thenSt, elseSt) =>
        if (!typeEquivalence(typecheck(cond), BooleanType()))
          error(s"if statements must have conditions that evaluate to bools")
        typecheck(thenSt, expected_type)
        if (elseSt != null) typecheck(elseSt, expected_type)

      case WhileSt(cond, stmt) =>
        if (!typeEquivalence(typecheck(cond), BooleanType()))
          error(s"while loops must have conditions that evaluate to bools")
        typecheck(stmt, expected_type)

      case LoopSt(stmt) => typecheck(stmt, expected_type)

      case ForSt(v, initial, step, increment, stmt) =>
        if (!typeEquivalence(typecheck(initial), IntType()) || !typeEquivalence(typecheck(step), IntType()) || !typeEquivalence(typecheck(increment), IntType()))
          error(s"For loop initial values, end values, and increment values must be ints")
        
        st.begin_scope()
        st.insert(v, VarDeclaration(IntType(), 0, 0))
        typecheck(stmt, expected_type)
        st.end_scope()

      case ExitSt() => ()

      case ReturnSt() => if (!expected_type.isInstanceOf[NoType]) error(s"Function is expected to return $expected_type")
      case ReturnValueSt(v) =>
        if (expected_type.isInstanceOf[NoType]) error("Function cannot have return value, as it returns nothing")
        val retT = typecheck(v)
        if (!typeEquivalence(retT, expected_type)) error(s"Function was expected to return $expected_type but instead returns $retT")

      case BlockSt(decls, stmts) =>
        st.begin_scope()
        decls.foreach(typecheck)
        stmts.foreach(stmt => typecheck(stmt, expected_type))
        st.end_scope()
        
      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck a definition */
  def typecheck ( e: Definition ) {
    trace(e,e match {
      case FuncDef(f,ps,ot,b)
        => st.insert(f,FuncDeclaration(ot,ps,"",0,0))
           st.begin_scope()
           ps.foreach{ case Bind(v,tp) => st.insert(v,VarDeclaration(tp,0,0)) }
           typecheck(b,ot)
           st.end_scope()

      /* PUT YOUR CODE HERE */
      case TypeDef(name, t) => st.insert(name, TypeDeclaration(t))

      case VarDef(name, t, v) =>
        val actualT = typecheck(v)
        if (!typeEquivalence(t, actualT)) error(s"var was defined as $t but was initialized to $actualT")
        val typeToUse = t match {
          case AnyType() => actualT
          case _ => t
        }
        st.insert(name, VarDeclaration(typeToUse, 0, 0))
    } )
  }

  /** typecheck the main program */
  def typecheck ( e: Program ) {
    typecheck(e.body,NoType())
  }
}
