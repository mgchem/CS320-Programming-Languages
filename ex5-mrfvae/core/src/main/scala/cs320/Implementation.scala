package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr): Value = {
    def interpEnv(e: Expr, env: Env): Value = e match {
      case Num(_) => _
      case Add(_, _)
    }
  }

}
