package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr): Value = {
    def binOp(op: (BigInt, BigInt) => BigInt): (Value, Value) => IntV = {
      case (IntV(n), IntV(m)) => IntV(op(n, m))
      case (x, y) => error()
    }

    def interpEnv(e: Expr, env: Env): Value = e match {
      case Id(x) => env.getOrElse(x, error())
      case IntE(n) => IntV(n)
      case BooleanE(b) => BooleanV(b)
      case Add(l, r) =>
        val lv = interpEnv(l, env)
        val rv = interpEnv(r, env)
        binOp(_ + _)(lv, rv)
      case Mul(l, r) =>
        val lv = interpEnv(l, env)
        val rv = interpEnv(r, env)
        binOp(_ * _)(lv, rv)
      case Div(l, r) =>
        val lv = interpEnv(l, env)
        val rv = interpEnv(r, env)
        if (rv == IntV(0)) {
          error()
        } else {
          binOp(_ / _)(lv, rv)
        }
      case Mod(l, r) =>
        val lv = interpEnv(l, env)
        val rv = interpEnv(r, env)
        if (rv == IntV(0)) {
          error()
        } else {
          binOp(_ % _)(lv, rv)
        }
      case Eq(l, r) =>
        val lv = interpEnv(l, env)
        lv match {
          case IntV(n) =>
            val rv = interpEnv(r, env)
            rv match {
              case IntV(m) => interpEnv(BooleanE(n == m), env)
              case _ => error()
            }
          case _ => error()
        }
      case Lt(l, r) =>
        val lv = interpEnv(l, env)
        lv match {
          case IntV(n) =>
            val rv = interpEnv(r, env)
            rv match {
              case IntV(m) => interpEnv(BooleanE(n < m), env)
              case _ => error()
            }
          case _ => error()
        }
      case If(c, t, f) =>
        interpEnv(c, env) match {
          case BooleanV(cv) =>
            if (cv) {
              interpEnv(t, env)
            } else {
              interpEnv(f, env)
            }
          case _ => error()
        }
      case TupleE(elist) =>
        val vlist = elist.map(interpEnv(_, env))
        TupleV(vlist)
      case Proj(e, idx) =>
        val TupleV(v) = interpEnv(e, env)
        v.apply(idx - 1)
      case NilE => NilV
      case ConsE(h, t) =>
        val v1 = interpEnv(h, env)
        val v2 = interpEnv(t, env)
        ConsV(v1, v2)
      case Empty(e) =>
        val v = interpEnv(e, env)
        v match {
          case NilV => BooleanV(true)
          case _ => BooleanV(false)
        }
      case Head(e) =>
        val ConsV(h, _) = interpEnv(e, env)
        h
      case Tail(e) =>
        val ConsV(_, t) = interpEnv(e, env)
        t
      case Val(x, e1, e2) =>
        val v1 = interpEnv(e1, env)
        interpEnv(e2, env + (x -> v1))
      case Fun(plist, b) =>
        CloV(plist, b, env)
      case RecFuns(dflist, b) =>
        val flist = dflist.map({
          case FunDef(x, plist, bo) =>
            val cloV = CloV(plist, bo, env)
            val nenv = env + (x -> cloV)
            cloV.env = nenv
            cloV
            })
        interpEnv(b, flist.apply(0).env)
      case App(f, alist) =>
        val CloV(plist, b, fenv) = interpEnv(f, env)
        val avlist = alist.map(interpEnv(_, env))
        interpEnv(b, fenv ++ (plist zip avlist).toMap)
      case Test(e, t) =>
        val v = interpEnv(e, env)
        v match {
          case IntV(_) => BooleanV(t == IntT)
          case BooleanV(_) => BooleanV(t == BooleanT)
          case TupleV(_) => BooleanV(t == TupleT)
          case NilV => BooleanV(t == ListT)
          case ConsV(_, _) => BooleanV(t == ListT)
          case CloV(_, _, _) => BooleanV(t == FunctionT)
        }
    }
    interpEnv(expr, Map())
  }
}
