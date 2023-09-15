package cs320

object Implementation extends Template {

  def volumeOfCuboid(a: Int, b: Int, c: Int): Int = a * b * c

  def concat(x: String, y: String): String = x + y

  def addN(n: Int): Int => Int = (x: Int) => x + n

  def twice(f: Int => Int): Int => Int = (x: Int) => f(f(x))

  def compose(f: Int => Int, g: Int => Int): Int => Int = (x: Int) => f(g(x))

  def double(l: List[Int]): List[Int] = l match {
    case Nil => Nil
    case h :: t => h * 2 :: double(t)
  }

  def sum(l: List[Int]): Int = l match {
    case Nil => 0
    case h :: t => h + sum(t)
  }

  def getKey(m: Map[String, Int], s: String): Int = m.get(s) match {
    case None => error(s)
    case _ => m.get(s).getOrElse(0)
  }

  def countLeaves(t: Tree): Int =
  t match {
    case br: Branch => countLeaves(br.left) + countLeaves(br.right)
    case le: Leaf => 1
  }

  def flatten(t: Tree): List[Int] =
  t match {
    case br: Branch => flatten(br.left) ++ List(br.value) ++ flatten(br.right)
    case le: Leaf => le.value :: Nil
  }
}
