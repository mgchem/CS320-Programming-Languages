package cs320

object Implementation extends Template {

  // apply a binary numeric function on all the combinations of numbers from
  // the two input lists, and return the list of all the results
  def binOp(
    op: (Int, Int) => Int,
    ls: List[Int],
    rs: List[Int]
  ): List[Int] = ls match {
    case Nil => Nil
    case l :: rest =>
      def f(r: Int): Int = op(l, r)
      rs.map(f) ++ binOp(op, rest, rs)
  }

  def interp(expr: Expr): List[Int] = {
    def interpEnv(e: Expr, env: Map[String, List[Int]]): List[Int]= e match {
      case Num(values) => values
      case Add(left, right) =>
        def AddOp(x: Int, y: Int): Int = x + y
        binOp(AddOp, interpEnv(left, env), interpEnv(right, env))
      case Sub(left, right) =>
        def SubOp(x: Int, y: Int): Int = x - y
        binOp(SubOp, interpEnv(left, env), interpEnv(right, env))
      case Val(name: String, expr: Expr, body: Expr) => 
        val Upenv = env + (name -> interpEnv(expr, env))
        interpEnv(body, Upenv)
      case Id(id) => if (env contains id) env.getOrElse(id, List()) else error("free identifier")
      case Min(left, mid, right) =>
        interpEnv(left, env) match {
          case Nil => Nil
          case l :: lrest =>
            interpEnv(mid, env) match {
              case Nil => Nil
              case m :: mrest =>
                def f(x: Int): Int = List(l, m, x).min
                interpEnv(right, env).map(f) ++ interpEnv(Min(Num(List(l)), Num(mrest), right), env) ++ interpEnv(Min(Num(lrest), mid, right), env)
            }
        }
      case Max(left, mid, right) =>
        interpEnv(left, env) match {
          case Nil => Nil
          case l :: lrest =>
            interpEnv(mid, env) match {
              case Nil => Nil
              case m :: mrest =>
                def f(x: Int): Int = List(l, m, x).max
                interpEnv(right, env).map(f) ++ interpEnv(Max(Num(List(l)), Num(mrest), right), env) ++ interpEnv(Max(Num(lrest), mid, right), env)
            }
        }
    }
    interpEnv(expr, Map())
  }
}