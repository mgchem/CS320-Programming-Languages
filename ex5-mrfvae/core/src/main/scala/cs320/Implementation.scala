package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr): Value = {
    def interpEnv(e: Expr, env: Env): Value = e match {
      case Num(n) => NumV(n)
      case Add(l, r) =>
        val NumV(n) = interpEnv(l, env)
        val NumV(m) = interpEnv(r, env)
        NumV(n + m)
      case Sub(l, r) =>
        val NumV(n) = interpEnv(l, env)
        val NumV(m) = interpEnv(r, env)
        NumV(n - m)
      case Val(x, v, b) => interpEnv(b, env + (x -> interpEnv(v, env)))
      case Id(x) => env(x)
      case App(f, al) => interpEnv(f, env) match {
        case CloV(pl, b, fenv) =>
          if (pl.length == al.length) {
            interpEnv(b, fenv ++ (pl zip al.map(interpEnv(_, env))).toMap)
          } else {
            error("wrong arity")
          }
        case _ => error("not a closure")
      }
      case Fun(pl, b) => CloV(pl, b, env)
      case Rec(m) =>
        RecV(m.map{case (k, v) => (k, interpEnv(v, env))})
      case Acc(e, n) => interpEnv(e, env) match {
        case RecV(e) => e.getOrElse(n, error("no such field"))
        case _ => error("not a record")
      }
    }

    interpEnv(expr, Map())
  }
}
