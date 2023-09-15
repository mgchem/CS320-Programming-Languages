package cs320

object Implementation extends Template {

  def freeIds(expr: Expr): Set[String] = expr match {
    case Num(_) => Set()
    case Add(l, r) => freeIds(l) | freeIds(r)
    case Sub(l, r) => freeIds(l) | freeIds(r)
    case Id(id) => Set(id)
    case Val(n, e, b) => freeIds(b) &~ Set(n) | freeIds(e)
  }

  def bindingIds(expr: Expr): Set[String] = expr match {
    case Num(_) => Set()
    case Add(l, r) => bindingIds(l) | bindingIds(r)
    case Sub(l, r) => bindingIds(l) | bindingIds(r)
    case Id(_) => Set()
    case Val(n, e, b) => Set(n) | bindingIds(e) | bindingIds(b)
  }

  def boundIds(expr: Expr): Set[String] = expr match {
    case Num(_) => Set()
    case Add(l, r) => boundIds(l) | boundIds(r)
    case Sub(l, r) => boundIds(l) | boundIds(r)
    case Id(_) => Set()
    case Val(n, e, b) => freeIds(b) & Set(n) | boundIds(b) | boundIds(e)
  }
}
