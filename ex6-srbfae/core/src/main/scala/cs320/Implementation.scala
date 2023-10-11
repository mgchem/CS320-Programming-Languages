package cs320

import Value._

object Implementation extends Template {

  type Sto = Map[Addr, Value]

  def interp(expr: Expr): Value = {
    def interp1(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match {
      case Num(n) => (NumV(n), sto)
      case Add(l, r) =>
        val (NumV(n), ls) = interp1(l, env, sto)
        val (NumV(m), rs) = interp1(r, env, ls)
        (NumV(n + m), rs)
      case Sub(l, r) =>
        val (NumV(n), ls) = interp1(l, env, sto)
        val (NumV(m), rs) = interp1(r, env, ls)
        (NumV(n - m), rs)
      case Id(x) => (env.getOrElse(x, error("free id")), sto)
      case Fun(p, b) => (CloV(p, b, env), sto)
      case App(f, a) => interp1(f, env, sto) match {
        case (CloV(x, b, fenv), ls) =>
          val (v, rs) = interp1(a, env, ls)
          interp1(b, fenv + (x -> v), rs)
        case _ => error("not a closure")
      }
      case NewBox(e) =>
        val (v, s) = interp1(e, env, sto)
        val a = s.keys.maxOption.getOrElse(0) + 1
        (BoxV(a), s + (a -> v))
      case SetBox(b, e) =>
        val (BoxV(a), bs) = interp1(b, env, sto)
        val (v, es) = interp1(e, env, bs)
        (v, es + (a -> v))
      case OpenBox(b) =>
        val (bv, bs) = interp1(b, env, sto)
        bv match {
          case BoxV(addr) =>
            val v = bs.getOrElse(addr, error("unallocated address"))
            (v, bs)
          case v => error("not a box")
        }
      case Seqn(l, rs) =>
        val initial = interp1(l, env, sto)
        rs.foldLeft(initial) {
          case ((v, s), r) => interp1(r, env, s)
        }
      case Rec(fs) =>
        val (fields, s) = fs.foldLeft(Map[String, Addr](), sto) {
          case ((m0, s0), (f, e)) =>
            val (v, s1) = interp1(e, env, s0)
            val addr = s1.keys.maxOption.getOrElse(0) + 1
            val s2 = s1 + (addr -> v)
            val m1 = m0 + (f -> addr)
            (m1, s2)
        }
        (RecV(fields), s)
      case Get(r, f) =>
        val (rv, rs) = interp1(r, env, sto)
        rv match {
          case RecV(m) =>
            val a = m.getOrElse(f, error("no such field"))
            val v = rs(a)
            (v, rs)
          case _ => error("not a record")
        }
      case Set(r, f, e) =>
        val (rv, rs) = interp1(r, env, sto)
        rv match {
          case RecV(m) =>
            val a = m.getOrElse(f, error("no such field"))
            val (v, s) = interp1(e, env, rs)
            (v, s + (a -> v))
          case _ => error("not a record")
        }
    }
    val (inter, s) = interp1(expr, Map(), Map())
    inter
  }
}
