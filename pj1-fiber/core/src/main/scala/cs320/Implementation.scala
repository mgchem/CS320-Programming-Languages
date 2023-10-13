package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr): Value = {
    def binOp(op: (BigInt, BigInt) => BigInt): (Value, Value) => IntV = {
      case (IntV(n), IntV(m)) => IntV(op(n, m))
      case (x, y) => error()
    }

    def interpEnv(e: Expr, env: Env): Value = e match {
      case Id(x) => env.getOrElse(x, error("1"))
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
          case _ => error("2")
        }
      case TupleE(elist) =>
        val vlist = elist.map(interpEnv(_, env))
        TupleV(vlist)
      case Proj(e, idx) =>
        interpEnv(e, env) match {
          case TupleV(v) =>
            if (v.length < idx) {
            error()
            } else {
            v.apply(idx - 1)
            }
          case _ => error()
        }
      case NilE => NilV
      case ConsE(h, t) =>
        val v1 = interpEnv(h, env)
        interpEnv(t, env) match {
          case ConsV(th, tt) =>
            ConsV(v1, ConsV(th, tt))
          case NilV => ConsV(v1, NilV)
          case _ => error()
        }
      case Empty(e) =>
        val v = interpEnv(e, env)
        v match {
          case NilV => BooleanV(true)
          case ConsV(_, _) => BooleanV(false)
          case _ => error()
        }
      case Head(e) =>
        interpEnv(e, env) match {
          case ConsV(h, _) => h
          case _ => error()
        }
      case Tail(e) =>
        interpEnv(e, env) match {
          case ConsV(_, t) => t
          case _ => error()
        }
      case Val(x, e1, e2) =>
        val v1 = interpEnv(e1, env)
        interpEnv(e2, env + (x -> v1))
      case Fun(plist, b) =>
        CloV(plist, b, env)
      case RecFuns(dflist, b) =>
        val temp = CloV(List(""), NilE, env)
        val flist = dflist.map({
          case FunDef(x, plist, bo) =>
            val cloV = CloV(plist, bo, env)
            temp.env += (x -> cloV)
            cloV
          }
        )
        for (v <- flist) {
          v.env = temp.env
        }
        interpEnv(b, temp.env)
      case App(f, alist) =>
        interpEnv(f, env) match {
          case CloV(plist, b, fenv) =>
            val avlist = alist.map(interpEnv(_, env))
            if (plist.length == avlist.length) {
              interpEnv(b, fenv ++ (plist zip avlist).toMap)
            } else {
              error()
            }
          case _ => error("3")
        }
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
