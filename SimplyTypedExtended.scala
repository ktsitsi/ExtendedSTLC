package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._
import scala.util.parsing.combinator.PackratParsers

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTypedExtended extends  StandardTokenParsers with PackratParsers{
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*", "+",
                              "=>", "|")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd", "fix", "letrec",
                              "case", "of", "inl", "inr", "as")


//~~~~~~~~~~~~~Parser Segment~~~~~~~~~~~~~~~~~
  type PP[+T] = PackratParser[T]
  lazy val Term: PP[Term] = appl | notApp
  //application
  lazy val appl: PP[App] = Term ~ notApp ^^ { case left ~ right => App(left, right) }
  //not application
  def notApp: Parser[Term] = (
    v
    |conditional
    |predecessor
    |successor
    |iszero
    |parens
    |variable
    |let
    |pair
    |sum
    |fixcombinator
    |letrec
  )
  def conditional: Parser[Term] = ("if" ~> Term) ~ ("then" ~> Term) ~ ("else" ~> Term) ^^ { case a ~ b ~ c => {If(a,b,c)}}
  def successor: Parser[Term] = "succ" ~> Term ^^ {s => Succ(s)}
  def predecessor: Parser[Term] = "pred" ~> Term ^^ {s => Pred(s)}
  def iszero: Parser[Term] = "iszero" ~> Term ^^ {s => IsZero(s)}
  def parens: Parser[Term] = "(" ~> Term <~ ")"
  def variable: Parser[Var] = ident ^^ Var
  def let: Parser[Term] = ("let" ~> ident) ~ (":" ~> ftype) ~ ("=" ~> Term) ~ ("in" ~> Term) ^^ {case let_var ~ let_ftype ~ let_term1 ~ let_term2 => App(Abs(let_var,let_ftype,let_term2),let_term1)} 
  def pair: Parser[Term] = (
    ("{" ~> Term) ~ "," ~ (Term <~ "}") ^^ {case p1 ~ "," ~ p2 => TermPair(p1,p2)}
    |"fst" ~> Term ^^{case f => First(f)}
    |"snd" ~> Term ^^{case s => Second(s)}
  )
  def sum:Parser[Term] = (
    ("inl" ~> Term) ~ ("as" ~> ftype) ^^ {case t ~ typ => Inl(t,typ)}  //inject left
    |("inr" ~> Term) ~ ("as" ~> ftype) ^^ {case t ~ typ => Inr(t,typ)} //inject right
    | ("case" ~> Term ) ~ "of" ~ ("inl" ~> ident) ~ ("=>" ~> Term) ~ "|" ~ ("inr" ~> ident) ~ ("=>" ~> Term) ^^ {case t ~ "of" ~ x1 ~ t1 ~ "|" ~ x2 ~ t2 => Case(t,x1,t1,x2,t2)}   //case
  )
  def fixcombinator: Parser[Term] = "fix" ~> Term ^^ {case t => Fix(t)}
  def letrec: Parser[Term] = ("letrec" ~> ident) ~ (":" ~> ftype) ~ ("=" ~>Term) ~ ("in" ~> Term) ^^ {case let_var ~ let_ftype ~ let_term1 ~ let_term2 => App(Abs(let_var,let_ftype,let_term2),Fix(Abs(let_var,let_ftype,let_term1)))}
  //Values
  def v: Parser[Term] = (
    "true" ^^ {x => True()}
    |"false" ^^ {x => False()}
    |nv
    |"\\" ~> ident ~ ":" ~ ftype ~ "." ~ Term ^^ { case v ~ ":" ~ t ~ "." ~ e  => Abs(v,t,e)}
    |("{" ~> v) ~ "," ~ (v <~ "}") ^^ {case p1 ~ "," ~ p2 => TermPair(p1,p2)}
    |("inl" ~> v) ~ ("as" ~> ftype) ^^ {case p1 ~ p2 => Inl(p1,p2)}
    |("inr" ~> v) ~ ("as" ~> ftype) ^^ {case p1 ~ p2 => Inr(p1,p2)}
  )
  def nv: Parser[Term] = (numericLit ^^ {_.toInt}) ^^ {
    case 0 => Zero()
    case a => rec_succ(a)               
  }

  //Fold Functions Associativity Precedence
  def rec_succ(x:Int):Term = if (x == 0) Zero() else Succ(rec_succ(x-1))
  def reduce(r: Type ~ String ,x: Type): Type = r match {
    case y ~ "*" => TypePair(y,x)
    case y ~ "->" => TypeFun(y,x)
    case y ~ "+" => TypeSum(y,x)
    case _ => throw new MatchError("illegal case: " +r)
  }

  //Typing Rules
  def ftype: Parser[Type] = rep(term ~ "->") ~ term ^^ {case list ~ last => (list :\ last)(reduce)}
  def term: Parser[Type] = rep(factor ~ ("*"|"+")) ~ factor ^^ {case list ~ last => (list :\ last)(reduce)}
  def factor: Parser[Type] = (
    "Nat" ^^ {x => TypeNat} 
    |"Bool" ^^ {x => TypeBool}
    |"(" ~> ftype <~ ")"
  )



 //~~~~~~~~~~~~~~Evaluation Segment~~~~~~~~~~~~~~~~~~~~

  //!!!!!!!!!!!!!Completed!!!!!!!!!!!!!!!!!!!!!
  def fv (t: Term): Set[String] = t match {
    case Var(name) => Set(name)
    case Zero() => Set("")
    case True() => Set("")
    case False() => Set("")
    case App(t1,t2) => fv(t1) union fv(t2)
    case Abs(bound,abs_t,t1) => fv(t1) - bound
    case IsZero(z) => fv(z)
    case Succ(s) => fv(s)
    case Pred(p) => fv(p)
    case If(c,b1,b2) => fv(c) union fv(b1) union fv(b2)
    case First(fp) => fv(fp)
    case Second(sp) => fv(sp)
    case TermPair(tp1,tp2) => fv(tp1) union fv(tp2)
    case Inl(il,_) => fv(il)
    case Inr(ir,_) => fv(ir)
    case Case(ct,cx1,ct1,cx2,ct2) => fv(ct)
    case Fix(fixt) => fv(fixt)
  }

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */
   
   def newVar(bound:String,bounded_vars:Set[String]): String = {
        val possible = (('a' to 'z').toSet ++ ('A' to 'Z')).map(_.toString) &~ bounded_vars
        if (possible.isEmpty){
          bound ++ "'"
        }
        else{
          possible.head
        }
    }
   def rename_rec(b:String,t:Term,n:String):Term = {
    if(fv(t) contains b){
      t match{
        case Var(name) => Var(n)
        case App(t1,t2) => App(rename_rec(b,t1,n),rename_rec(b,t2,n))
        case Abs(b1,abs_t,body) => Abs(b1,abs_t,rename_rec(b,body,n)) 
      }
    }
    else{t}
   }

  def alpha(t: Term,nv:String): Term = t match{
    /*We are sure that the input term is a lambda abstraction so we dont
    need to check it*/
    case Abs(bound,abs_t,body) => {
      //return the converted term
      Abs(nv,abs_t,rename_rec(bound,body,nv))
    }
    case _ => t
  }

  /** Straight forward substitution method
   *  (see definition 5.3.5 in TAPL book).
   *  [x -> s]t
   *
   *  @param t the term in which we perform substitution
   *  @param x the variable name
   *  @param s the term we replace x with
   *  @return  ...
   */

  //!!!!!!!!!!!!!!!!!Not Completed!!!!!!!!!!!!!!!!
  def subst(t: Term, x: String, s: Term): Term = t match{
    case Var(name) => if(name == x){s} else{Var(name)}
    case App(t1,t2) => App(subst(t1,x,s),subst(t2,x,s))
    case Abs(bound,abs_t,body) => {
      //println("I am in abs substitution bound=",bound,"x=",x,"body=",body,"s=",s)

      if(bound == x) {Abs(bound,abs_t,body)}
      else if(bound != x && (((fv(s) contains bound)== false)| ((fv(body) contains x) == false))){
        //println("mesa")
        Abs(bound,abs_t,subst(body,x,s))
      }
      else{
        val renamed = newVar(bound,fv(body) union fv(s))
        subst(alpha(Abs(bound,abs_t,body),renamed),x,s)
      }
    }
    case IsZero(z) => IsZero(subst(z,x,s))
    case If(cond,b1,b2) => If(subst(cond,x,s),subst(b1,x,s),(subst(b2,x,s)))
    case Succ(s_arg) => Succ(subst(s_arg,x,s))
    case Pred(p_arg) => Pred(subst(p_arg,x,s))
    case True() => True()
    case False() => False()
    case Zero() => Zero()
    case TermPair(tp1,tp2) => TermPair(subst(tp1,x,s),subst(tp2,x,s))
    case First(fp) => First(subst(fp,x,s))
    case Second(sp) => Second(subst(sp,x,s))
    case Inl(il,ity) => Inl(subst(il,x,s),ity)  //What about different types
    case Inr(ir,ity) => Inr(subst(ir,x,s),ity)
    case Case(ct,cx1,ct1,cx2,ct2) => Case(subst(ct,x,s),cx1,ct1,cx2,ct2)
    case Fix(fixt) => Fix(subst(fixt,x,s))
  }


  //Completed
  def isNumeric(term:Term): Boolean = term match{
    case Zero() => true
    case Succ(nv) => isNumeric(nv)
    case _ => false
  }

  def isValue(term: Term): Boolean = term match {
    case _: Abs  => true
    case _: True => true
    case _: False => true
    case _: Zero => true
    case Succ(nv) => isNumeric(nv)
    case TermPair(tp1,tp2) => isValue(tp1) && isValue(tp2)
    case Inl(il1,_) => isValue(il1)
    case Inr(ir1,_) => isValue(ir1)
    case _       => false
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case True() => throw new NoRuleApplies(t)
    case False() => throw new NoRuleApplies(t)
    case Var(var_name) => throw new NoRuleApplies(t)
    case Zero() => throw new NoRuleApplies(t)
    case _: Abs => throw new NoRuleApplies(t)
    case If(cond,t1,t2) => {cond match {
      case True() => t1
      case False() => t2
      case if_rdc => If(reduce(if_rdc),t1,t2)
      }
    }
    case IsZero(z) => {z match {
        case Zero() => True()
        case Succ(zs) if isNumeric(zs) => False()
        case z_rdc => IsZero(reduce(z_rdc))
      }
    }
    case Pred(p) =>{p match {
      case Zero() => Zero()
      case Succ(ps) if isNumeric(ps) => ps
      case p_rdc => Pred(reduce(p_rdc)) 
      }
    }
    case Succ(s) => Succ(reduce(s))
    //case App(app_t1,app_t2) => reduceCallByValue(t)
    case App(Abs(argDef,abs_t,body), arg) if isValue(arg) => {//println("Term CBV:1",t)
                                                              subst(body,argDef,arg)
                                                              }
    case App(fun, arg) if isValue(fun) => App(fun, reduce(arg))
    case App(fun, arg) => {//println("Term CBV:3",t)
                          App(reduce(fun), arg)
                          }
    case First(fp) => fp match{
      case TermPair(tp1,tp2) if (isValue(tp1)) => tp1
      case _ => First(reduce(fp))
    }
    case Second(sp) => sp match{
      case TermPair(stp1,stp2) if (isValue(stp2)) => stp2
      case _ => Second(reduce(sp))
    }
    case TermPair(rtp1,rtp2) => if (isValue(rtp1)) TermPair(rtp1,reduce(rtp2)) else TermPair(reduce(rtp1),rtp2)
    case Inl(il,ity) => Inl(reduce(il),ity)
    case Inr(ir,ity) => Inr(reduce(ir),ity)
    case Case(t,x1,t1,x2,t2) => t match{
      case Inl(arg,_) if (isValue(arg)) => subst(t1,x1,arg)
      case Inr(arg,_) if (isValue(arg)) => subst(t2,x2,arg) 
      case _=> Case(reduce(t),x1,t1,x2,t2)
    }
  case Fix(ft) => ft match{
    case Abs(x,typ1,t2) => subst(t2,x,Fix(ft))
    case _ => Fix(reduce(ft))
  }

  }


  def addbinding(ctx:Context,var_name:String,ty:Type): Context = (var_name,ty)::ctx
  def getTypefromCtx(ctx:Context,var_name:String): Type = ctx.find(bind => bind._1 == var_name).getOrElse(throw new TypeError(Var(var_name),"Untypable"))._2
  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  //~~~~~~~~~~~~~~~Type Checker~~~~~~~~~~~~~~~~~~~~~~~~~~~
  def typeof(ctx: Context, t: Term): Type = t match {
    case True() => TypeBool
    case False() => TypeBool
    case Zero() => TypeNat
    case If(cond,branch1,branch2) => if (typeof(ctx,cond) == TypeBool && typeof(ctx,branch1) == typeof(ctx,branch2)) typeof(ctx,branch1) else throw new TypeError(t,"Not typable")
    case Succ(s) => if (typeof(ctx,s) == TypeNat) TypeNat else throw new TypeError(t,"Untypable")
    case Pred(p) => if (typeof(ctx,p) == TypeNat) TypeNat else throw new TypeError(t,"Untypable")
    case IsZero(z) => if (typeof(ctx,z) == TypeNat) TypeBool else throw new TypeError(t,"Untypable")
    case TermPair(tp1,tp2) => TypePair(typeof(ctx,tp1),typeof(ctx,tp2))
    case First(f) => typeof(ctx,f) match{
      case TypePair(tpt1,tpt2) => tpt1
      case _ => throw new TypeError(t,"Untypable")
    }
    case Second(sec) => typeof(ctx,sec) match{
      case TypePair(tpt1,tpt2) => tpt2
      case _ => throw new TypeError(t,"Untypable")
    }
    case Var(v) => getTypefromCtx(ctx,v)
    case Abs(bound,typ,body) => TypeFun(typ,typeof(addbinding(ctx,bound,typ),body))
    case App(t1,t2) => typeof(ctx,t1) match{
      case TypeFun(typ11,typ12) => if (typeof(ctx,t2) == typ11) typ12 else throw new TypeError(t,"Untypable")
      case _ => throw new TypeError(t,"Untypable")
    }
    case Inl(inl,inlt) => inlt match {
      case TypeSum(tps1,tps2) => if (typeof(ctx,inl) == tps1) TypeSum(tps1,tps2) else throw new TypeError(t,"Untypable")
      case _ => throw new TypeError(t,"Untypable")
    }
    case Inr(inr,inrt) => inrt match {
      case TypeSum(tpsr1,tpsr2) => if (typeof(ctx,inr) == tpsr2) TypeSum(tpsr1,tpsr2) else throw new TypeError(t,"Untypable")
      case _ => throw new TypeError(t,"Untypable")
    }
    case Case(ct,cx1,ct1,cx2,ct2) => typeof(ctx,ct) match {
      case TypeSum(ts1,ts2) => if (typeof(addbinding(ctx,cx1,ts1),ct1) == typeof(addbinding(ctx,cx2,ts2),ct2)) typeof(addbinding(ctx,cx2,ts2),ct2) else throw new TypeError(t,"Untypable")     
      case _ => throw new TypeError(t,"Untypable")
    }
    case Fix(fxt) => typeof(fxt) match {
      case TypeFun(fxa,fxb) => if (fxa == fxb) fxa else throw new TypeError(t,"Untypable")
      case _ => throw new TypeError(fxt,"Untypable")
    }
  }

  def typeof(t: Term): Type = try {
    typeof(Nil, t)
  } catch {
    case err @ TypeError(_, _) =>
      Console.println(err)
      null
  }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("parsed: " + trees)
          //println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
