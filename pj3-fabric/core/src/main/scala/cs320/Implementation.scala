package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)

  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._

    case class TEnv(
      vars: Map[String, (List[VarT], Type, Boolean)],
      tbinds: Map[String, TypeDef]
    ) {
      def add(x: String, a: List[VarT], t: Type, mut: Boolean): TEnv = TEnv(vars + (x -> (a, t, mut)), tbinds)
      def add(x: String, td: TypeDef): TEnv = TEnv(vars, tbinds + (x -> td))
    }

    def typeCheck(expr: Expr): Type = {
      def wfType(ty: Type, tenv: TEnv): Unit = ty match {
        case IntT => ()
        case BooleanT => ()
        case UnitT => ()
        case ArrowT(ptlist, r) =>
          ptlist.foreach(pt => wfType(pt, tenv))
          wfType(r, tenv)
        case VarT(a) =>
          if (!tenv.vars.contains(a)) error()
          else ()
        case AppT(x, tlist) =>
          tlist.foreach(targ => wfType(targ, tenv))
          val td = tenv.tbinds.getOrElse(x, error())
          td match {
            case TypeDef(_, alist, _) =>
              if (tlist.length == alist.length) ()
              else error()
            case _ => error()
          }
        case _ => error()
      }

      def recXTlist(xtl: List[(String, Type)], tenv: TEnv): TEnv = xtl match {
        case Nil => tenv
        case h :: t =>
          val px = h._1
          val pt = h._2
          recXTlist(t, tenv.add(px, Nil, pt, false))
      }

      def wfRecDef(rdlist: List[RecDef], tenv: TEnv): Unit = rdlist match {
        case Nil => ()
        case h :: t => h match {
          case RecFun(x, alist, plist, rt, b) =>
            val tlist = xl_to_tl(alist)
            val xtlist = alist.zip(tlist)
            val ntenv = recXTlist(xtlist, tenv)
            val nntenv = recXTlist(plist, ntenv)
            val bt = typeCheck(b, nntenv)
            unify(bt, rt)
            wfRecDef(t, tenv)
          case TypeDef(x, alist, vlist) =>
            val tlist = xl_to_tl(alist)
            val xtlist = alist.zip(tlist)
            val ntenv = recXTlist(xtlist, tenv)
            def rec(tl: List[Type], tenv: TEnv): Unit = tl match {
              case Nil => ()
              case h :: t =>
                wfType(h, tenv)
                rec(t, tenv)
            }
            for (v <- vlist) {
              val vtlist = v.params
              rec(vtlist, ntenv)
            }
            wfRecDef(t, tenv)
          case _ => ()
        }
      }

      def occurs(t1: VarT, t2: Type): Boolean = t2 match {
        case IntT => false
        case BooleanT => false
        case UnitT => false
        case ArrowT(l, r) =>
          def rec(tlist: List[Type]): Boolean = tlist match {
            case Nil => false
            case h :: t =>
              occurs(t1, h) || rec(t)
          }
          rec(l) || occurs(t1, r)
        case t2 @ VarT(_) => t1 eq t2
        case AppT(_, targs) =>
          def rec(tlist: List[Type]): Boolean = tlist match {
            case Nil => false
            case h :: t =>
              occurs(t1, h) || rec(t)
          }
          rec(targs)
      }

      def unify(t1: Type, t2: Type): Unit = (t1, t2) match {
        case (t1 @ VarT(_), t2) =>
          if (t1 eq t2)
            ()
          else if (occurs(t1, t2))
            error()
          else
            ()
        case (t1, t2 @ VarT(_)) => unify(t2, t1)
        case (IntT, IntT) => ()
        case (BooleanT, BooleanT) => ()
        case (ArrowT(tlist1, t3), ArrowT(tlist2, t4)) =>
          unify(t3, t4)
          if (tlist1.length != tlist2.length) error()
          for (i <- 0 until tlist1.length) {
            if (tlist1(i) != tlist2(i)) error()
          }
          ()
        case (IntT, _: ArrowT) => error()
        case (_: ArrowT, IntT) => error()
        case _ => error()
      }

      def substitute(tau: Type, submap: Map[VarT, Type]): Type = tau match {
        case IntT => tau
        case BooleanT => tau
        case UnitT => tau
        case ArrowT(ptypes, rtype) =>
          val nptypes = ptypes.map({
            case ptype => substitute(ptype, submap)
          })
          val nrtype = substitute(rtype, submap)
          ArrowT(nptypes, nrtype)
        case AppT(name, targs) =>
          val ntargs = targs.map({
            case targ => substitute(targ, submap)
          })
          AppT(name, ntargs)
        case VarT(name) => submap.getOrElse(VarT(name), VarT(name))
      }

      def typeofCase(c: Case, tenv: TEnv, vlist: List[Variant], alist: List[String], tlist: List[Type]): Type = c match {
        case Case(x, xlist, e) =>
          if (alist.length != tlist.length) error()
          for (v <- vlist if v.name == x) {
            val vtlist = v.params
            if (xlist.length != vtlist.length) error()
            val atlist = xl_to_tl(alist)
            val mapping = atlist.zip(tlist).toMap
            val subtlist = vtlist.map(vt => substitute(vt, mapping))
            val addmaplist = subtlist.map(ty => (Nil, ty, false))
            val nenv = TEnv(tenv.vars ++ (xlist zip addmaplist).toMap, tenv.tbinds)
            typeCheck(e, nenv)
          }
          UnitT
        case _ => error()
      }

      def xl_to_tl(xlist: List[String]): List[VarT] = {
        val tlist = xlist.map({
          case x => VarT(x)
        })
        tlist
      }

      def recdefEnv(rdlist: List[RecDef], tenv: TEnv): TEnv = rdlist match {
        case Nil => tenv
        case h :: t => h match {
          case Lazy(x, tau, e) =>
            wfType(tau, tenv)
            val ntenv = tenv.add(x, Nil, tau, false)
            val et = typeCheck(e, ntenv)
            unify(tau, et)
            recdefEnv(t, ntenv)
          case RecFun(x, alist, plist, rt, _) =>
            val tlist = plist.map({
              case (_, tau) => tau
            })
            recdefEnv(t, tenv.add(x, xl_to_tl(alist), ArrowT(tlist, rt), false))
          case d @ TypeDef(x, alist, vlist) =>
            if (tenv.tbinds.contains(x)) error()
            val ntenv = tenv.add(x, d)
            def rec(vl: List[Variant], tenv: TEnv): TEnv = vlist match {
              case Nil => tenv
              case h :: t =>
                val tlist = xl_to_tl(alist)
                if (h.params == Nil) {
                  rec(t, tenv.add(h.name, tlist, AppT(x, tlist), false))
                }
                else rec(t, tenv.add(h.name, tlist, ArrowT(h.params, AppT(x, tlist)), false))
            }
            val nntenv = rec(vlist, ntenv)
            recdefEnv(t, nntenv)
        }
      }

      def typeCheck(e: Expr, tenv: TEnv): Type = e match {
        case Id(x, targs) =>
          for (targ <- targs) wfType(targ, tenv)
          val (alist, tau, _) = tenv.vars.getOrElse(x, error())
          if (alist.length != targs.length) error()
          val mapping = (alist zip targs).toMap
          substitute(tau, mapping)
        case IntE(n) => IntT
        case BooleanE(b) => BooleanT
        case UnitE => UnitT
        case Add(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          unify(lt, IntT)
          unify(rt, IntT)
          IntT
        case Mul(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          unify(lt, IntT)
          unify(rt, IntT)
          IntT
        case Div(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          unify(lt, IntT)
          unify(rt, IntT)
          IntT
        case Mod(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          unify(lt, IntT)
          unify(rt, IntT)
          IntT
        case Eq(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          unify(lt, IntT)
          unify(rt, IntT)
          BooleanT
        case Lt(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          unify(lt, IntT)
          unify(rt, IntT)
          BooleanT
        case Sequence(l, r) =>
          val lt = typeCheck(l, tenv)
          val rt = typeCheck(r, tenv)
          rt
        case If(c, t, f) =>
          val ct = typeCheck(c, tenv)
          unify(ct, BooleanT)
          val tt = typeCheck(t, tenv)
          unify(tt, typeCheck(f, tenv))
          tt
        case Val(m, x, taup, e, b) =>
          taup match {
            case Some(tau) =>
              wfType(tau, tenv)
              val et = typeCheck(e, tenv)
              unify(tau, et)
              val nenv = tenv.add(x, Nil, et, m)
              typeCheck(b, nenv)
            case _ =>
              val et = typeCheck(e, tenv)
              val nenv = tenv.add(x, Nil, et, m)
              typeCheck(b, nenv)
          }
        case RecBinds(dflist, b) => IntT
        case Fun(plist, b) =>
          for ((x, tau) <- plist) {
            wfType(tau, tenv)
          }
          val xlist = plist.map({
            case (x, _) => x
          })
          val addlist = plist.map({
            case (_, tau) =>
              (Nil, tau, false)
          })
          val tlist = plist.map({
            case (_, tau) => tau
          })
          val nenv = TEnv(tenv.vars ++ (xlist zip addlist).toMap, tenv.tbinds)
          val bt = typeCheck(b, nenv)
          ArrowT(tlist, bt)
        case Assign(x, e) =>
          val (alist, tau, mut) = tenv.vars.getOrElse(x, error())
          if (alist.length != 0) error()
          if (!mut) error()
          val et = typeCheck(e, tenv)
          unify(tau, et)
          UnitT
        case App(f, args) =>
          val ft = typeCheck(f, tenv)
          ft match {
            case ArrowT(ptypes, rtype) if args.length == ptypes.length =>
              ptypes.zip(args).foreach(tup => unify(tup._1, typeCheck(tup._2, tenv)))
              rtype
            case _ => error()
          }
        case Match(e, clist) =>
          val et = typeCheck(e, tenv)
          et match {
            case AppT(tau, targs) =>
              tenv.tbinds.getOrElse(tau, error()) match {
                case TypeDef(t, alist, vlist) =>
                  if (targs.length != alist.length) error()
                  if (clist.length != vlist.length) error()
                  val ctlist = clist.map({
                    case c => typeofCase(c, tenv, vlist, alist, targs)
                  })
                  val ct1 = ctlist.head
                  for (ct <- ctlist) {
                    unify(ct, ct1)
                  }
                  ct1
                case _ => error()
              }
            case _ => error()
          }
      }
      typeCheck(expr, TEnv(Map(), Map()))
    }
  }

  object U {
    import Untyped._

    def interp(expr: Expr): Value = {
      type Sto = Map[Addr, Value]

      def binOp(op: (BigInt, BigInt) => BigInt): (Value, Value) => IntV = {
        case (IntV(n), IntV(m)) => IntV(op(n, m))
        case (x, y) => error()
      }

      def recEnv(rdlist: List[RecDef], env: Env, sto: Sto): Env = rdlist match {
        case Nil => env
        case h :: t => h match {
          case Lazy(x, e) =>
            val a = sto.keys.maxOption.getOrElse(0) + 1
            recEnv(t, env + (x -> a), sto + (a -> ExprV(UnitE, Map())))
          case RecFun(x, plist, b) =>
            val a = sto.keys.maxOption.getOrElse(0) + 1
            recEnv(t, env + (x -> a), sto + (a -> CloV(plist, b, env)))
          case TypeDef(vlist) =>
            def rec(vl: List[Variant], env: Env, sto: Sto): (Env, Sto) = vl match {
              case Nil => (env, sto)
              case h :: t =>
                val a = sto.keys.maxOption.getOrElse(0) + 1
                if (h.empty) {
                  rec(t, env + (h.name -> a), sto + (a -> VariantV(h.name, Nil)))
                }
                else {
                  rec(t, env + (h.name -> a), sto + (a -> ConstructorV(h.name)))
                }
            }
            val (nenv, nsto) = rec(vlist, env, sto)
            recEnv(t, nenv, nsto)
        }
      }

      def recSto(rdlist: List[RecDef], env: Env, sto: Sto): Sto = rdlist match {
        case Nil => sto
        case h :: t => h match {
          case Lazy(x, e) =>
            val a = env.getOrElse(x, error())
            recSto(t, env, sto + (a -> ExprV(e, env)))
          case RecFun(x, plist, b) =>
            val a = env.getOrElse(x, error())
            recSto(t, env, sto + (a -> CloV(plist, b, env)))
          case TypeDef(vlist) =>
            def rec(vl: List[Variant], env: Env, sto: Sto): (Env, Sto) = vl match {
              case Nil => (env, sto)
              case h :: t =>
                val a = env.getOrElse(h.name, error())
                if (h.empty) {
                  rec(t, env, sto + (a -> VariantV(h.name, Nil)))
                }
                else {
                  rec(t, env, sto + (a -> ConstructorV(h.name)))
                }
            }
            val (nenv, nsto) = rec(vlist, env, sto)
            recSto(t, nenv, nsto)
        }
      }

      def recMat(xvl: List[(String, Value)], env: Env, sto: Sto): (Env, Sto) = xvl match {
        case Nil => (env, sto)
        case h :: t =>
          val a = sto.keys.maxOption.getOrElse(0) + 1
          recMat(t, env + (h._1 -> a), sto + (a -> h._2))
      }

      def interp(e: Expr, env: Env, sto: Sto): (Value, Sto) = e match {
        case Id(x) =>
          val a = env.getOrElse(x, error())
          val v = sto.getOrElse(a, error())
          v match {
            case ExprV(cape, capenv) =>
              val (cv, csto) = interp(cape, capenv, sto)
              (cv, csto + (a -> cv))
            case _ => (v, sto)
          }
        case IntE(n) => (IntV(n), sto)
        case BooleanE(b) => (BooleanV(b), sto)
        case UnitE => (UnitV, sto)
        case Add(l, r) =>
          val (lv, ls) = interp(l, env, sto)
          val (rv, rs) = interp(r, env, ls)
          (binOp(_ + _)(lv, rv), rs)
        case Mul(l, r) =>
          val (lv, ls) = interp(l, env, sto)
          val (rv, rs) = interp(r, env, ls)
          (binOp(_ * _)(lv, rv), rs)
        case Div(l, r) =>
          val (lv, ls) = interp(l, env, sto)
          val (rv, rs) = interp(r, env, ls)
          (lv, rv) match {
            case (IntV(ln), IntV(rn)) =>
              if (rn != 0) (IntV(ln / rn), rs)
              else error()
            case _ => error()
          }
        case Mod(l, r) =>
          val (lv, ls) = interp(l, env, sto)
          val (rv, rs) = interp(r, env, ls)
          (lv, rv) match {
            case (IntV(ln), IntV(rn)) =>
              if (rn != 0) (IntV(ln % rn), rs)
              else error()
            case _ => error()
          }
        case Eq(l, r) =>
          val (lv, ls) = interp(l, env, sto)
          lv match {
            case IntV(n) =>
              val (rv, rs) = interp(r, env, ls)
              rv match {
                case IntV(m) =>
                  if (n == m) {
                    (BooleanV(true), rs)
                  }
                  else (BooleanV(false), rs)
                case _ => error()
              }
            case _ => error()
          }
        case Lt(l, r) =>
          val (lv, ls) = interp(l, env, sto)
          lv match {
            case IntV(n) =>
              val (rv, rs) = interp(r, env, ls)
              rv match {
                case IntV(m) =>
                  if (n < m) {
                    (BooleanV(true), rs)
                  }
                  else (BooleanV(false), rs)
                case _ => error()
              }
            case _ => error()
          }
        case Sequence(l, r) =>
          val (_, ls) = interp(l, env, sto)
          interp(r, env, ls)
        case If(c, t, f) =>
          interp(c, env, sto) match {
            case (BooleanV(cv), cs) =>
              if (cv == true) {
                interp(t, env, cs)
              }
              else interp(f, env, cs)
            case _ => error()
          }
        case Val(x, e, b) =>
          val (ev, es) = interp(e, env, sto)
          val a = es.keys.maxOption.getOrElse(0) + 1
          interp(b, env + (x -> a), es + (a -> ev))
        case RecBinds(dflist, b) =>
          val nenv = recEnv(dflist, env, sto)
          val nsto = recSto(dflist, nenv, sto)
          interp(b, nenv, nsto)
        case Fun(plist, b) => (CloV(plist, b, env), sto)
        case Assign(x, e) =>
          val a = env.getOrElse(x, error())
          val (ev, es) = interp(e, env, sto)
          (UnitV, es + (a -> ev))
        case App(f, alist) =>
          val (fv, fs) = interp(f, env, sto)
          def rec(al: List[Expr], avl: List[Value], tsto: Sto): (Value, Sto) = al match {
            case Nil => fv match {
              case CloV(plist, b, fenv) =>
                if (plist.length == avl.length) {
                  val a = tsto.keys.maxOption.getOrElse(0) + 1
                  val adlist = (a until (avl.length + a)).toList
                  interp(b, fenv ++ (plist zip adlist).toMap, tsto ++ (adlist zip avl).toMap)
                }
                else error()
              case ConstructorV(x) => (VariantV(x, avl), tsto)
              case _ => error()
            }
            case h :: t =>
              val (hv, hs) = interp(h, env, tsto)
              val navl = avl :+ hv
              rec(t, navl, hs)
          }
          rec(alist, Nil, fs)
        case Match(e, clist) =>
          val (ev, _) = interp(e, env, sto)
          ev match {
            case VariantV(vx, vlist) =>
              val cxlist = clist.map({
                case c => c.variant
              })
              val mc = clist(cxlist.indexOf(vx))
              if (mc.names.length != vlist.length) error()
              val xvlist = mc.names.zip(vlist)
              val (nenv, nsto) = recMat(xvlist, env, sto)
              interp(mc.body, nenv, nsto)
            case _ => error()
          }
      }
      val (v, s) = interp(expr, Map(), Map())
      v
    }
  }
}
