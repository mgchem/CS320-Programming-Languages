package cs320

object Implementation extends Template {

  def typeCheck(e: Typed.Expr): Typed.Type = T.typeCheck(e)

  def interp(e: Untyped.Expr): Untyped.Value = U.interp(e)

  object T {
    import Typed._

    trait TEnv
    case class vars(env: Map[String, (Type, Boolean)]) extends TEnv
    case class tbinds(env: Map[String, Map[String, Type]]) extends TEnv

    def add(v: vars, x: String, t: Type, m: Boolean): TEnv = vars + (x -> (t, m))
    def add(tb: tbinds, x: String, m: Map[String, Type]): TEnv = tbinds + (x -> m)
    def contains(x: String): Boolean = tbinds.contains(x)
    def inDomain(x: String): Boolean = vars.contains(x)

    def typeCheck(expr: Expr): Type = {
      def wfType(ty: Type, tenv: TEnv): Unit = ty match {
        case IntT => ()
        case BooleanT => ()
        case UnitT => ()
        case ArrowT(ptlist, r) =>
          for (tau<-ptlist) {
            wfType(tau, tenv)
          }
          wfType(r, tenv)
        case AppT(t, tlist) =>
          for (tau<-tlist) {
            wfType(tau, tenv)
          }
          if (!tenv.contains(t)) error()
          tenv(t) match {
            case AppT(tp, alist) =>
              if (tlist.length != alist.length) {
                error()
              } else ()
            case _ => error()
          }
        case VarT(a) =>
          if (!tenv.contains(a)) error()
        case _ => error()
      } 

      def resolve(ty: Type): Type = ty match {
        case VarT(None) => ty
        case VarT(Some(t)) => resolve(t)
        case _ => ty
      }

      def occurs(t1: VarT, t2: Type): Boolean = resolve(t2) match {
        case IntT => false
        case ArrowT(l, r) => occurs(t1, l) || occurs(t1, r)
        case t2 @ VarT(_) => t1 eq t2
      }

      def unify(t1: Type, t2: Type): Unit = (resolve(t1), resolve(t2)) match {
        case (t1 @ VarT(_), t2) =>
          if (t1 eq t2)
            ()
          else if (occurs(t1, t2))
            error()
          else
            t1.ty = Some(t2)
        case (t1, t2 @ VarT(_)) => unify(t2, t1)
        case (IntT, IntT) => ()
        case (ArrowT(tlist1, t3), ArrowT(tlist2, t4)) =>
          unify(t3, t4)
          if (tlist1.length != tlist2.length) error()
          for (i<-((0 until tlist1.length).toList)) {
            if (tlist1[i] != tlist2[i]) error()
          }
        case (IntT, _: ArrowT) => error()
        case (_: ArrowT, IntT) => error()
      }

      def typeCheck(e: Expr, tenv: Env): Type = e match {
        case Id(x, targs) =>
          tenv.getOrElse(x, error())
        case IntE(n) => IntT
        case BooleanE(b) => BooleanT
        case UnitE => UnitT
        case Add(l, r) =>
          unify(typeCheck(l, tenv), IntT)
          unify(typeCheck(r, tenv), IntT)
          IntT
        case Mul(l, r) =>
          unify(typeCheck(l, tenv), IntT)
          unify(typeCheck(r, tenv), IntT)
          IntT
        case Div(l, r) =>
          unify(typeCheck(l, tenv), IntT)
          unify(typeCheck(r, tenv), IntT)
          IntT
        case Mod(l, r) =>
          unify(typeCheck(l, tenv), IntT)
          unify(typeCheck(r, tenv), IntT)
          IntT
        case Eq(l, r) =>
          unify(typeCheck(l, tenv), IntT)
          unify(typeCheck(r, tenv), IntT)
          BooleanT
        case Lt(l, r) =>
          unify(typeCheck(l, tenv), IntT)
          unify(typeCheck(r, tenv), IntT)
          BooleanT
        case Sequence(l, r) => typeCheck(r, tenv)
        case If(c, t, f) =>
          unify(typeCheck(c, tenv), BooleanT)
          val ty = typeCheck(t, tenv)
          unify(ty, typeCheck(f, tenv))
          ty
        case Val(m, x, ty, e, b) =>
          if (ty != VarT(None)) wfType(ty, tenv)
          val tau1 = typeCheck(e, tenv)
          if ((ty != VarT(None)) && tau1 != ty) error()
          typeCheck(b, tenv + (x -> (tau1, m))) 
        case RecBinds(dlist, b) =>
          for (rd<-dlist) rd match {
            case TypeDef(t, alist, vlist) =>
              if (tenv.contains(t)) error()
              UnitT
            case _ => error()
          }
        case Fun(plist, b) =>
          val tlist = List[Type]
          for ((x, (tau, m))<-plist) {
            wfType(tau, tenv)
            tlist :+ tau
            tenv.add(ArrowT(x, tau))
          }
          ArrowT(tlist, typeCheck(b, tenv))
        case Assign(x, e) =>
          if (!tenv.contains(x)) error()
          tenv(x) match {
            case (VarT(a), m) => error()
            case (tau, m) =>
              unify(tau, typeCheck(e, tenv))
              UnitT
            case _ => error()
          }
        case App(f, alist) =>
          val resT = VarT(None)
          unify(ArrowT(typeCheck(alist, tenv), resT), typeCheck(f, tenv))
          resT
        case Match(e, clist) =>
          typeCheck(e, tenv) match {
            case AppT(x, tlist) =>
              if (!tenv.contains(x)) error()
              UnitT
            case _ => error()
          }
      }
      typeCheck(expr, TEnv(Map()))
    }
  }

  object U {
    import Untyped._

    def interp(expr: Expr): Value = {
      def interp(e: Expr, env: Env): Value = e match {
        case Id(n) => UnitV
        case IntE(value: BigInt) => UnitV
        case BooleanE(value: Boolean) => UnitV
        case UnitE => UnitV
        case Add(left: Expr, right: Expr) => UnitV
        case Mul(left: Expr, right: Expr) => UnitV
        case Div(left: Expr, right: Expr) => UnitV
        case Mod(left: Expr, right: Expr) => UnitV
        case Eq(left: Expr, right: Expr) => UnitV
        case Lt(left: Expr, right: Expr) => UnitV
        case Sequence(left: Expr, right: Expr) => UnitV
        case If(cond: Expr, texpr: Expr, fexpr: Expr) => UnitV
        case Val(name: String, expr: Expr, body: Expr) => UnitV
        case RecBinds(defs: List[RecDef], body: Expr) => UnitV
        case Fun(params: List[String], body: Expr) => UnitV
        case Assign(name: String, expr: Expr) => UnitV
        case App(fun: Expr, args: List[Expr]) => UnitV
        case Match(expr: Expr, cases: List[Case]) => UnitV
      }
      interp(expr, Map())
    }
  }
}
