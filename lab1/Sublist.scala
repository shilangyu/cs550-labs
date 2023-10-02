//> using scala "3.2.0"
//> using jar "stainless-library_2.13-0.9.8.1.jar"
//> using options "-Wconf:msg=pattern.*?specialized:s,msg=not.*?exhaustive:s"

import stainless.lang._
import stainless.collection._
import stainless.annotation._

/*
 * The definition of List and its operations can be found here:
 * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala
 * You should not need them, but you can find some lemmas on List here:
 * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/ListSpecs.scala
 */

def sublist[T](l1: List[T], l2: List[T]): Boolean = {
  (l1, l2) match {
    case (Nil(), _) => true
    case (_, Nil()) => false
    case (Cons(x, xs), Cons(y, ys)) =>
      (x == y && sublist(xs, ys)) || sublist(l1, ys)
  }
}

@extern
@main
def main(): Unit = {
  def example(lhs: List[Int], rhs: List[Int]): Unit = {
    println(s"${lhs.toScala.mkString("<", ",", ">")} ⊑ ${rhs.toScala
        .mkString("<", ",", ">")} = ${sublist(lhs, rhs)}")
  }

  example(List(0, 2), List(0, 1, 2))
  example(List(0, 0, 2), List(0, 2))
  example(List(1, 0), List(0, 0, 1))
  example(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))
  example(List(25, 11, 53, 38), List(15, 25, 11, 8, 53, 22, 38))
}

object SublistSpecs {

  /* forall l, sublist(l, l) */
  def reflexivity[T](l: List[T]): Unit = {
    if !l.isEmpty then
      reflexivity(l.tail)
  }.ensuring(_ => sublist(l, l))

  def leftTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && sublist(l1, l2))

    if sublist(l1, l2.tail) then
      leftTail(l1, l2.tail)
  }.ensuring(_ =>
    sublist(l1.tail, l2)
  )
 
  def tails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && sublist(l1, l2))
    if sublist(l1, l2.tail) then 
      leftTail(l1, l2.tail)
  }.ensuring(_ =>
    sublist(l1.tail, l2.tail)
  )
  
  /* forall l1 l2 l3, sublist(l1, l2) /\ sublist(l2, l3) ==> sublist(l1, l3) */
  def transitivity[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(sublist(l1, l2) && sublist(l2, l3))
    l1 match
      case Nil() => ()
      case Cons(x, xs) =>
        val (Cons(y, ys), Cons(z, zs)) = (l2, l3)
        if x == y && y == z then
          tails(l1, l2)
          tails(l2, l3)
          transitivity(l1.tail, l2.tail, l3.tail)
        else if x != y && sublist(l1, l2.tail) then
          leftTail(l2, l3)
          transitivity(l1, l2.tail, l3)
        else if y != z && sublist(l2, l3.tail) then
          transitivity(l1, l2, l3.tail)
  }.ensuring(_ =>
    sublist(l1, l3)
  )
  
  def lengthHomomorphism[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2))
    l1 match
      case Nil() => ()
      case Cons(x, xs) =>
        if sublist(l1, l2.tail) then
          lengthHomomorphism(l1, l2.tail)
        else
          lengthHomomorphism(xs, l2.tail)
  }.ensuring(_ =>
    l1.length <= l2.length
  )

  def biggerSublist[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2) && l1.length >= l2.length)
    lengthHomomorphism(l1, l2)
    l1 match
      case Nil() => ()
      case Cons(x, xs) =>
        biggerSublist(xs, l2.tail)
  }.ensuring(_ =>
    l1 == l2
  )
  
  def antisymmetry[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2) && sublist(l2, l1))
    lengthHomomorphism(l1, l2)
    lengthHomomorphism(l2, l1)
    biggerSublist(l1, l2)
  }.ensuring(_ =>
    l1 == l2
  )

  /*
   * ++ is the list concatenation operator.
   * It is defined here:
   * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala#L46
   */
  def extendRight[T](l1: List[T], l2: List[T]): Unit = {
    l1 match
      case Nil() => ()
      case Cons(x, xs) =>
        extendRight(xs, l2)
  }.ensuring(_ =>
    sublist(l1, l1 ++ l2)
  )

  def extendLeft[T](l1: List[T], l2: List[T]): Unit = {
    l1 match
      case Nil() =>
        reflexivity(l2)
      case Cons(x, xs) =>
        extendLeft(xs, l2)
  }.ensuring(_ =>
    sublist(l2, l1 ++ l2)
  )

  def prepend[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2))
    l match
      case Nil() => ()
      case Cons(z, zs) =>
        prepend(zs, l1, l2)
  }.ensuring(_ =>
    sublist(l ++ l1, l ++ l2)
  )

  def append[T](l1: List[T], l2: List[T], l: List[T]): Unit = {
    require(sublist(l1, l2))

    (l1, l2) match
      case (Nil(), Nil()) => reflexivity(l)
      case (Nil(), _)     => extendLeft(l2, l)
      case (_, Nil())     => extendLeft(l1, l)
      case (Cons(h1, tail1), Cons(h2, tail2)) =>
        if h1 == h2 then
          tails(l1, l2)
          append(tail1, tail2, l)
        else append(l1, tail2, l)
  }.ensuring(_ => sublist(l1 ++ l, l2 ++ l))
}
