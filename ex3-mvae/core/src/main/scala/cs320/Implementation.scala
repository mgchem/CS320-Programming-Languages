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
      def f(r: Int): Int = ???
      rs.map(f) ++ binOp(op, rest, rs)
  }

  def interp(expr: Expr): List[Int] = ???
}
