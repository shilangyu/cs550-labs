import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*
import stainless.lang.Map.ToMapOps

import Utils.*
import Formulas.*

object Resolution {

  /** Make sure that all bound variables are uniquely named, and with names
    * different from free variables. This will simplify a lot future
    * transformations. The specific renaming can be arbitrary.
    */
  def makeVariableNamesUnique(f: Formula): Formula = {
    /*
     * A generator of fresh names
     * Any call to `get` should be followed by a call to `next`
     */
    case class FreshNames(i: BigInt) {
      require(i >= 0)

      // Return a fresh identifier
      def get: Identifier = Synthetic(i)
      // Update (functionally) this generator
      def next = FreshNames(i + 1)
    }

    def mVNUForm(
        subst: Map[Identifier, Term]
    )(f: Formula, freshId0: FreshNames): (Formula, FreshNames) = {
      decreases(f)
      f match {
        case Predicate(name, children) =>
          (Predicate(name, children.map(t => t.substitute(subst))), freshId0)
        case And(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (And(nLeft, nRight), freshId2)
        case Or(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (Or(nLeft, nRight), freshId2)
        case Implies(left, right) =>
          val (nLeft, freshId1) = mVNUForm(subst)(left, freshId0)
          val (nRight, freshId2) = mVNUForm(subst)(right, freshId1)
          (Implies(nLeft, nRight), freshId2)
        case Neg(inner) =>
          val (nInner, freshId1) = mVNUForm(subst)(inner, freshId0)
          (Neg(nInner), freshId1)
        case Forall(Var(id), inner) =>
          val x = Var(freshId0.get)
          val p = mVNUForm(subst + ((id, x)))(inner, freshId0.next)
          (Forall(x, p._1), p._2)
        case Exists(Var(id), inner) =>
          val x = Var(freshId0.get)
          val p = mVNUForm(subst + ((id, x)))(inner, freshId0.next)
          (Exists(x, p._1), p._2)
      }
    }

    // Generate fresh names for free variables
    val (alreadyTaken, freshId) = statefulLeftMap(
      f.freeVariables,
      FreshNames(0),
      (v: Identifier, id: FreshNames) => ((v, Var(id.get): Term), id.next)
    )
    mVNUForm(alreadyTaken.toMap)(f, freshId)._1
  }

  /* Part one: transforming formulas */

  /*
   * Put the formula in Negation Normal Form.
   */
  def negationNormalForm(f: Formula): Formula = {
    def aux(f: Formula, neg: Boolean): Formula = {
      decreases(f)
      f match {
        case p: Predicate =>
          if neg then Neg(p) else p
        case And(left, right) =>
          if neg then Or(aux(left, true), aux(right, true)) else And(aux(left, false), aux(right, false))
        case Or(left, right) =>
          if neg then And(aux(left, true), aux(right, true)) else Or(aux(left, false), aux(right, false))
        case Implies(left, right) =>
          if neg then And(aux(left, false), aux(right, true)) else Or(aux(left, true), aux(right, false))
        case Neg(inner) =>
          aux(inner, !neg)
        case Forall(v, inner) =>
          if neg then Exists(v, aux(inner, true)) else Forall(v, aux(inner, false))
        case Exists(v, inner) =>
          if neg then Forall(v, aux(inner, true)) else Exists(v, aux(inner, false))
      }
    }
    aux(f, false)
  }.ensuring(res => res.isNNF)

  /** Perform the following steps:
    *   - Make variable names unique (using [[makeVariableNamesUnique]]);
    *   - Put the formula in negation normal form (using
    *     [[negationNormalForm]]);
    *   - Eliminate existential quantifiers using Skolemization.
    */
  def skolemizationNegation(f0: Formula): Formula = {
    def aux(f: Formula, subst: Map[Identifier, Term]): Formula = {  // subst should be Var -> Function ...
      decreases(f)
      f match {
        case Predicate(id, children) =>
          Predicate(id, children.map(_.substitute(subst)))
        case And(left, right) =>
          And(aux(left, subst), aux(right, subst))
        case Or(left, right) =>
          Or(aux(left, subst), aux(right, subst))
        case _: Implies => ???
        case Neg(inner) =>
          Neg(aux(inner, subst))
        case Forall(v, inner) =>
          Forall(v, aux(inner, subst))
        case e @ Exists(v, inner) =>
          aux(inner, subst + (v.name -> Function(v.name, e.freeVariables.map(Var(_)))))
      }
    }
    aux(negationNormalForm(makeVariableNamesUnique(f0)), Map.empty)
  }.ensuring(res => res.isNNF && res.containsNoExistential)

  /** Perform the following steps:
    *   - Put the formula in negation normal, skolemized form (using
    *     [[skolemizationNegation]]);
    *   - Return the matrix of the formula.
    */
  def prenexSkolemizationNegation(f: Formula): Formula = {
    def aux(f: Formula): Formula = {
      decreases(f)
      f match {
        case p: Predicate => p
        case And(left, right) =>
          And(aux(left), aux(right))
        case Or(left, right) =>
          Or(aux(left), aux(right))
        case _: Implies => ???
        case Neg(inner) =>
          Neg(aux(inner))
        case Forall(v, inner) =>
          aux(inner)
        case _: Exists => ???
      }
    }
    aux(skolemizationNegation(f))
  }.ensuring(res =>
    res.isNNF && res.containsNoUniversal && res.containsNoExistential
  )

  /** Perform the following steps:
    *   - Put the formula in prenex, negation normal, skolemized form (using
    *     [[prenexSkolemizationNegation]]);
    *   - Put the formula in conjunctive normal form (CNF).
    *
    * Note that the formula might grow exponentially in size. If we only want to
    * preserve satisfiability, we could avoid it by introducing fresh variables.
    * This function should NOT do that.
    */
  def conjunctionPrenexSkolemizationNegation(f: Formula): List[Clause] = {
    def aux(f: Formula): List[Clause] = {
      f match
        case p: Predicate => List(List(Literal(p)))
        case And(l, r) =>
          aux(l) ++ aux(r)
        case Or(l, r) =>
          for
            cl <- aux(l)
            cr <- aux(r)
          yield cl ++ cr
        case _: Implies => ???
        case n @ Neg(inner) =>
          inner match
            case _: Predicate => List(List(Literal(n)))
            case _ => ???
        case _: Forall => ???
        case _: Exists => ???
    }
    aux(prenexSkolemizationNegation(f))
  }

  /* Part two: proof checking */

  /** A clause in a proof is either assumed, i.e. it is an hypothesis, or it is
    * deduced from previous clauses. A proof is written in a specific order, and
    * a justification should not refer to a subsequent step.
    */
  sealed abstract class Justification
  case object Assumed extends Justification
  case class Deduced(premises: (BigInt, BigInt), subst: Map[Identifier, Term])
      extends Justification

  type ResolutionProof = List[(Clause, Justification)]

  sealed trait ProofCheckResult {
    def valid = this match {
      case Valid      => true
      case Invalid(_) => false
    }
  }
  case object Valid extends ProofCheckResult
  case class Invalid(reason: String = "Unspecified") extends ProofCheckResult {
    @extern
    override def toString(): String = {
      reason
    }
  }

  /** Verify that [[proof]] is a valid proof, i.e. that every clause is
    * correctly justified (unless assumed). It is quite easy to miss some corner
    * cases. We thus recommend that you:
    *   - Have a look at the provided methods on Literal, as you will most
    *     likely need them;
    *   - "Keep It Simple, Stupid!": efficiency is not taken into account, so no
    *     need for fancy efficient checks;
    *   - On the other hand, checking that the conclusion of a resolution step
    *     is valid might be a bit more involved than it seems;
    *   - As a consequence of the previous point: add more tests;
    *   - You should return [[Valid]] when the proof is valid, and [[Invalid]]
    *     otherwise. In the latter case, you are free to set any string as the
    *     reason. Having precise failure reasons will help you a lot in the
    *     third part of this lab.
    *
    * Note: in order to use string interpolation in stainless, you need to wrap
    * it in an extern function, e.g.
    * @extern
    *   def mkErrorMessage = s"This is an error at step ${k}"
    *   Invalid(mkErrorMessage)
    */
  def checkResolutionProof(proof: ResolutionProof): ProofCheckResult = {
    proof.foldLeft((List.empty[Clause], Valid: ProofCheckResult)){ (current, step) => current match
      case (prefix, Valid) => step match
        case (clause, Assumed) => (prefix :+ clause, Valid)    
        case (clause, Deduced((a, b), subst)) =>
          if a < 0 || a >= prefix.length || b < 0 || b >= prefix.length then (prefix, Invalid("Premise indices out of range"))
          else
            val prema = prefix(a).map(_.substitute(subst)).toSet
            val premb = prefix(b).map(_.substitute(subst)).toSet
            val all =
              for
                la <- prema.toList
                lb <- premb.toList
              yield
                val (las, lbs) = (prema - la, premb - lb)
                la == lb.negation && (las ++ lbs) == clause.toSet  // We can freely remove duplicates, since (a v a) = a
            if all.foldLeft(false)(_ || _) then (prefix :+ clause, Valid)
            else (prefix, Invalid("Could not use resolution to derive the clause"))
      case x @ (_, _: Invalid) => x
    }._2
  }

  def assumptions(proof: ResolutionProof): List[Clause] = {
    proof
      .filter(_._2 match {
        case Assumed       => true
        case Deduced(_, _) => false
      })
      .map(_._1)
  }

  def conclusion(proof: ResolutionProof): Clause = {
    require(!proof.isEmpty)
    proof(proof.length - 1)._1
  }
  
  /* Part three: The Dreadsbury Mansion Mystery */
  object MansionFragments {
    import Mansion.*

    /** You can use the (scala) variable killer to refer to the killer E.g. of a
      * proof step using it: The killer is one of the characters (
      * List(eqv(killer, a), eqv(killer, b), eqv(killer, c)), Deduced((0, 5),
      * Map(id(1) -> killer)) )
      */

    def charlesInnocent: ResolutionProof = {
      List(
        (
          List(hates(a, a).negation, killed(c, a).negation),
          Deduced((6, 8), Map(id(2) -> c, id(3) -> a, id(4) -> a))
        ),
        (
          List(hates(a, a)),
          Deduced((10, 15), Map(id(6) -> a))
        ),
        (
          List(killed(c, a).negation),
          Deduced((21, 22), Map())
        )
      )
    }

    /*
     * k is the index your first step will have in the final proof.
     * You can use it to refer to previous steps relatively to this index,
     * so that your proof won't break if you go back and change your previous one.
     *
     * Mansion.buildFullProof contains all of the steps we implemented in your stead
     * and indexed them relatively to k.
     */
    def agathaKilledAgatha(k: BigInt): ResolutionProof = {
      List(
        (
          List(eqv(killer, a)),
          Deduced((k - 9, k - 1), Map())
        ),
        (
          List(killed(a, a)),
          Deduced((k - 11, k), Map(id(16) -> a))
        )
      )
    }
  }

  /*
   * To show that a formula phi is valid, we show that it's negation is unsatisfiable, i.e. !phi -> false.
   * Hence if a Proof contains an empty clause, then the negation of the conjunction of all assumed clauses has to be valid
   */
  def extractTheorem(proof: ResolutionProof): Formula = {
    require(
      !assumptions(proof).isEmpty && assumptions(proof).forall(!_.isEmpty)
    ) // Has "reasonable" assumptions
    require(proof.last._1 == Nil()) // Concludes unsat

    def toFormulas(clauses: List[Clause]): List[Formula] = {
      require(clauses.forall(!_.isEmpty))

      clauses match {
        case Nil()       => Nil()
        case Cons(c, cs) => Cons(or(c.map(_.get)), toFormulas(cs))
      }
    }

    val assumpts = toFormulas(assumptions(proof))
    assert(!assumpts.isEmpty)

    Neg(and(assumpts))
  }

}
