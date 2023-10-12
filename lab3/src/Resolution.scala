import Formulas.*
import Utils.*
import stainless.annotation.*
import stainless.collection.*
import stainless.lang.Map.ToMapOps
import stainless.lang.*

extension [T](l: List[T])
  def without(index: BigInt): List[T] = l.take(index) ++ l.drop(index + 1)
  def zipWithIndex: List[(T, BigInt)] = {
    def aux(l: List[T], i: BigInt): List[(T, BigInt)] = l match
      case Cons(h, t) => Cons((h, i), aux(t, i + 1))
      case Nil()      => Nil()

    aux(l, 0)
  }

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
    f match
      case Neg(inner) =>
        inner match
          case p @ Predicate(name, children) => Neg(p)
          case And(l, r) =>
            Or(negationNormalForm(Neg(l)), negationNormalForm(Neg(r)))
          case Or(l, r) =>
            And(negationNormalForm(Neg(l)), negationNormalForm(Neg(r)))
          case Implies(left, right) =>
            negationNormalForm(Neg(Or(Neg(left), right)))
          case Neg(inner) => negationNormalForm(inner)
          case Forall(variable, inner) =>
            Exists(variable, negationNormalForm(Neg(inner)))
          case Exists(variable, inner) =>
            Forall(variable, negationNormalForm(Neg(inner)))

      case p @ Predicate(name, children) => p
      case And(l, r) => And(negationNormalForm(l), negationNormalForm(r))
      case Or(l, r)  => Or(negationNormalForm(l), negationNormalForm(r))
      case Implies(left, right) => negationNormalForm(Or(Neg(left), right))
      case Forall(variable, inner) =>
        Forall(variable, negationNormalForm(inner))
      case Exists(variable, inner) =>
        Exists(variable, negationNormalForm(inner))
  }.ensuring(res => res.isNNF)

  /** Perform the following steps:
    *   - Make variable names unique (using [[makeVariableNamesUnique]]);
    *   - Put the formula in negation normal form (using
    *     [[negationNormalForm]]);
    *   - Eliminate existential quantifiers using Skolemization.
    */
  def skolemizationNegation(f0: Formula): Formula = {
    def aux(f: Formula, subst: Map[Identifier, Term]): Formula = f match
      case Predicate(name, children) =>
        Predicate(name, children.map(_.substitute(subst)))
      case And(l, r)               => And(aux(l, subst), aux(r, subst))
      case Or(l, r)                => Or(aux(l, subst), aux(r, subst))
      case Implies(left, right)    => ??? // should not happen in NNF
      case Neg(inner)              => Neg(aux(inner, subst))
      case Forall(variable, inner) => Forall(variable, aux(inner, subst))
      case e @ Exists(variable, inner) =>
        aux(
          inner,
          subst + (variable.name -> Function(
            variable.name,
            e.freeVariables.map(Var(_))
          ))
        )

    val f = negationNormalForm(makeVariableNamesUnique(f0))

    aux(f, Map())
  }.ensuring(res => res.isNNF && res.containsNoExistential)

  /** Perform the following steps:
    *   - Put the formula in negation normal, skolemized form (using
    *     [[skolemizationNegation]]);
    *   - Return the matrix of the formula.
    */
  def prenexSkolemizationNegation(f: Formula): Formula = {
    def aux(f: Formula): Formula = f match
      case p @ Predicate(name, children) => p
      case And(l, r)                     => And(aux(l), aux(r))
      case Or(l, r)                      => Or(aux(l), aux(r))
      case Implies(left, right)          => ??? // should not happen in NNF
      case Neg(inner)                    => Neg(aux(inner))
      case Forall(variable, inner)       => aux(inner)
      case Exists(variable, inner) =>
        ??? // should not happen after skolemization

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
    def aux(f: Formula): List[Clause] = f match
      case And(l, r) => aux(l) ++ aux(r)
      case Or(l, r) =>
        for
          cl <- aux(l)
          cr <- aux(r)
        yield cl ++ cr
      case p @ (Neg(Predicate(_, _)) | Predicate(_, _)) =>
        List(List(Literal(p)))
      case Implies(left, right)    => ??? // should not happen in NNF
      case Neg(inner)              => ??? // should not happen in NNF
      case Forall(variable, inner) => ??? // should not happen after prenex
      case Exists(variable, inner) =>
        ??? // should not happen after skolemization

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
    def checkStep(
        clauses: List[Clause],
        clause: Clause,
        step: Justification
    ): ProofCheckResult = step match
      case Assumed => Valid
      case Deduced((i1, i2), subst) =>
        val (c1, c2) = (
          clauses(i1).map(_.substitute(subst)),
          clauses(i2).map(_.substitute(subst))
        )

        c1.zipWithIndex
          .find((e) => {
            val (l1, i1) = e

            c2.indexOf(l1.negation) match
              case BigInt(-1) => false
              case i2 =>
                (c1.without(i1) ++ c2.without(i2)).toSet == clause.toSet
          })
          .map((_) => Valid)
          .getOrElse(Invalid("no steps found"))

    proof
      .foldLeft[(List[Clause], ProofCheckResult)]((List(), Valid))(
        (scan, curr) =>
          scan._2 match
            case Valid =>
              (scan._1 :+ curr._1, checkStep(scan._1, curr._1, curr._2))
            case i: Invalid => scan
      )
      ._2
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
        /* TODO: Complete me */
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
        /* TODO: Complete me */
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
