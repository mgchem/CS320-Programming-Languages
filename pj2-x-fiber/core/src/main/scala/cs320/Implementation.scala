package cs320

import Value._

object Implementation extends Template {

  def interp(expr: Expr): Value = {
    def binOp(op: (BigInt, BigInt) => BigInt): (Value, Value) => IntV = {
      case (IntV(n), IntV(m)) => IntV(op(n, m))
      case (x, y) => error()
    }

    trait Handler
    case object EmptyHandler extends Handler
    case class ObHandler(expr: Expr, env: Env, k: Cont, h: Handler) extends Handler

    def interp(e: Expr, eh: Handler, env: Env, k: Cont): Value = e match {
      case Id(x) => k(env.getOrElse(x, error()))
      case IntE(n) => k(IntV(n))
      case BooleanE(b) => k(BooleanV(b))
      case Add(l, r) =>
        interp(l, eh, env, lv =>
          interp(r, eh, env, rv =>
            k(binOp(_ + _)(lv, rv))))
      case Mul(l, r) =>
        interp(l, eh, env, lv =>
          interp(r, eh, env, rv =>
            k(binOp(_ * _)(lv, rv))))
      case Div(l, r) =>
        interp(l, eh, env, lv =>
          interp(r, eh, env, rv => {
            if (rv == IntV(0)) {
              error()
            } else {
              k(binOp(_ / _)(lv, rv))
            }
          }))
      case Mod(l, r) =>
        interp(l, eh, env, lv =>
          interp(r, eh, env, rv => {
            if (rv == IntV(0)) {
              error()
            } else {
              k(binOp(_ % _)(lv, rv))
            }
          }))
      case Eq(l, r) =>
        interp(l, eh, env, lv => lv match {
          case IntV(n) =>
            interp(r, eh, env, rv => rv match {
              case IntV(m) => k(interp(BooleanE(n == m), eh, env, Value => Value))
              case _ => error()
            })
          case _ => error()
        })
      case Lt(l, r) =>
        interp(l, eh, env, lv => lv match {
          case IntV(n) =>
            interp(r, eh, env, rv => rv match {
              case IntV(m) => k(interp(BooleanE(n < m), eh, env, Value => Value))
              case _ => error()
            })
          case _ => error()
        })
      case If(c, t, f) =>
        interp(c, eh, env, cv => cv match {
          case BooleanV(b) =>
            if (b) {
              interp(t, eh, env, k)
            } else {
              interp(f, eh, env, k)
            }
          case _ => error()
        })
      case TupleE(elist) =>
        def rec(el: List[Expr], evl: List[Value]): Value = el match {
          case Nil => k(TupleV(evl))
          case h :: t =>
            interp(el.head, eh, env, ehv => {
              val evll = evl :+ ehv
              rec(t, evll)
            })
        }
        rec(elist, Nil)
      case Proj(e, idx) =>
        interp(e, eh, env, ev => ev match {
          case TupleV(v) =>
            if (v.length < idx) {
            error()
            } else {
            k(v.apply(idx - 1))
            }
          case _ => error()
        })
      case NilE => k(NilV)
      case ConsE(h, t) =>
        interp(h, eh, env, hv =>
          interp(t, eh, env, tv => tv match {
            case ConsV(th, tt) =>
              k(ConsV(hv, ConsV(th, tt)))
            case NilV => k(ConsV(hv, NilV))
            case _ => error()
          }))
      case Empty(e) =>
        interp(e, eh, env, ev => ev match {
          case ConsV(_, _) =>
            k(BooleanV(false))
          case NilV => k(BooleanV(true))
          case _ => error()
        })
      case Head(e) =>
        interp(e, eh, env, ev => ev match {
          case ConsV(h, _) => k(h)
          case _ => error()
        })
      case Tail(e) =>
        interp(e, eh, env, ev => ev match {
          case ConsV(_, t) => k(t)
          case _ => error()
        })
      case Val(x, e, b) =>
        interp(e, eh, env, ev =>
          interp(b, eh, env + (x -> ev), bv => k(bv)))
      case Vcc(x, b) =>
        interp(b, eh, env + (x -> ContV(k)), k)
      case Fun(plist, b) =>
        k(CloV(plist, b, env))
      case RecFuns(dflist, b) =>
        val flist = dflist.map({
          case FunDef(f, plist, fb) =>
            CloV(plist, fb, env)
          })
        val ilist = dflist.map({
            case FunDef(f, plist, fb) => f
        })
        val tenv = (ilist zip flist).toMap
        for (v <- flist) {
          v.env = v.env ++ tenv
        }
        interp(b, eh, env ++ tenv, k)
      case App(f, alist) =>
        interp(f, eh, env, fv => {
          def rec(al: List[Expr], avl: List[Value]): Value = al match {
            case Nil =>
              fv match {
                case CloV(plist, b, fenv) =>
                  if (plist.length == avl.length) {
                    interp(b, eh, fenv ++ (plist zip avl).toMap, k)
                  } else {
                    error()
                  }
                case ContV(kv) =>
                  if (avl.length == 1) {
                    kv(avl.head)
                  } else {
                    error()
                  }
                case _ => error()
              }
            case h :: t =>
              interp(h, eh, env, ahv => {
                val avll = avl :+ ahv
                rec(t, avll)
              })
            }
          rec(alist, Nil)
        })
      case Test(e, t) =>
        interp(e, eh, env, ev => ev match {
          case IntV(_) => k(BooleanV(t == IntT))
          case BooleanV(_) => k(BooleanV(t == BooleanT))
          case TupleV(_) => k(BooleanV(t == TupleT))
          case NilV => k(BooleanV(t == ListT))
          case ConsV(_, _) => k(BooleanV(t == ListT))
          case CloV(_, _, _) => k(BooleanV(t == FunctionT))
          case ContV(_) => k(BooleanV(t == FunctionT))
        })
      case Throw(e) =>
        interp(e, eh, env, ev => eh match {
          case ObHandler(he, henv, hk, hh) =>
            interp(he, hh, henv, hev => hev match {
              case CloV(plist, b, fenv) =>
                if (plist.length == 1) {
                  interp(b, hh, fenv + (plist.head -> ev), hk)
                } else {
                  error()
                }
              case ContV(kv) =>
                kv(ev)
              case _ => error()
            })
          case EmptyHandler => error()
        })
      case Try(e, h) =>
        interp(e, ObHandler(h, env, k, eh), env, k)
    }
    interp(expr, EmptyHandler, Map(), v => v)
  }

}
