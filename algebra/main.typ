#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/theorion:0.4.1": *
#import "@preview/curryst:0.6.0": rule, prooftree, rule-set
#import "@preview/biceps:0.0.1": *
#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/wordometer:0.1.5": word-count, total-words
#import "@preview/cetz:0.4.2": draw

#show: word-count

#show: shorthands.with(
  ($|-$, math.tack),
  ($|=$, math.tack.double),
)
#import cosmos.rainbow: *
#show: show-theorion
// #set par.line(numbering: it => text(fill: gray, [#it]))
// #set page(numbering: "1 of 1")
#set page(numbering: none)
#set heading(numbering: "1.1.1.1")
#set math.equation(numbering: "(1)")
#show link: this => underline(text(this, fill: blue))

#set page(width: 8.5in, height: 11in)
// #set page(width: 8.5in, height: 205in)
// #set page(margin: (right: 3.0in))

#let opp(x) = $#x^sans("op")$
#let fwd = $sans("fwd")$
#let bwd = $sans("bwd")$
#let Set = $bold("Set")$
#let FinSet = $bold("FinSet")$
#let Hom = $bold("Hom")$
#let CC = $cal(C)$
#let PP = $cal(P)$
#let natrec = $sans("natrec")$
#let id = $sans("id")$
#let rev = $sans("rev")$
#let inl = $sans("inl")$
#let inr = $sans("inr")$
#let inv = $sans("inv")$
#let Ob = $sans("Ob")$
#let head = $sans("head")$
#let Prop = $sans("Prop")$
#let tail = $sans("tail")$
#let fst = $sans("fst")$
#let snd = $sans("snd")$
#let KK = $bold(sans("K"))$
#let DA = $sans("DA")$
#let oDA = $sans("oDA")$
#let mDA = $sans("mDA")$
#let rDA = $sans("rDA")$
#let Init = $sans("Init")$
#let Term = $sans("Term")$
#let TODO = text(fill: red, $bold(sans("TODO"))$)

#let (exercise-counter, exercise-box, exercise, show-exercise) = make-frame(
  "exercise",
  "Exercise",
  counter: none,
  inherited-levels: 2,
  inherited-from: heading,
  render: (prefix: none, title: "", full-title: auto, body) => [#strong[#full-title.]#sym.space#emph(body)],
)
#show: show-exercise

#align(center, [
  #heading(numbering: none, text(size: 1.5em)[Algebras and automata])

  Michael Zhang
])

= Algebras

// Before we look at coalgebras, let us consider algebras, which are slightly more intuitive.
In algebra, there are many interesting structures to study, such as groups, rings, vector spaces, etc.
If we look at the definitions for some common algebraic structures:

- A group is a tuple $(G, dot.op, (-)^(-1))$ satisfying some axioms.
- A ring is a tuple $(R, +, dot.op)$ satisfying some axioms.
- A boolean algebra is a tuple $(B, and, or, not)$ satisfying some axioms.

They all seem to look kind of familiar -- a carrier, usually a set, followed by some operations on that carrier, satisfying some axioms.
It may be useful to look for an abstraction over all of these.

In order to make it easier to think about abstractions for a universal algebra, we'll start by focusing our work in the category of sets $Set$.
So our carrier will be some object in $Set$.

Now, consider an endofunctor $F : Set -> Set$.
This will have two parts: an action on objects, which is simply a set function, and an action on morphisms.
If we take $X$ to be the input carrier set, then $F(X)$ is essentially the representation of _inputs_ to operations you can take with $X$.
Then, we have a morphism $alpha : F(X) -> X$, known as the _structure_ map, which defines how the operations take place.

For example:
- the identity element of a group is not dependent on anything, so we say $F(X) = 1$, and so the morphism $alpha : 1 -> X$ simply selects the identity element with no further input.
  // Note that this also requires a separate uniqueness axiom on the identity element.
- the inverse operation of a group is a set-function $X -> X$. This translates to our framework as $F(X) = X$ and so $alpha : X -> X$ in this case.
- the group operation is a binary set-function $(dot) : X times X -> X$. We have $F(X) = X times X$, so the morphism $alpha : X times X -> X$ has the correct type.

But each of these are still independent pieces of a group definition.
We must combine them somehow.
A single morphism $alpha : F(X) -> X$ must represent all actions you can possibly take on a group.
One answer would be to take $F(X) = 1 union.plus X union.plus X times X$, where $union.plus$ is the disjoint set-union operation.
This is usually written instead as $F(X) = 1 + X + X times X$, as we will soon generalize disjoint unions in $Set$ to coproducts in an arbitrary category.

So our combined morphism $alpha : F(X) -> X$ essentially gives us a choice of which operation we would like to take, as well as how each is implemented.
It should be clear at this point that each functor $F$ can possibly have multiple $alpha : F(X) -> X$.
This corresponds to the notion that there are multiple groups, multiple rings, multiple Boolean algebras, etc.

Of course, since $F$ is a functor, it must have an action on morphisms as well.
In the case of $F(X) = A times X + B$, a functor application to a morphism $F(X ->^f Y)$ would have type $A times X + B ->^F(f) A times Y + B$.
It may be useful to think of $F(f)$ as being a coproduct of morphisms $A times X ->^f_1 A times Y$ and $B ->^f_2 B$.
This is often true for the cases we will be studying, as many of the functors for the common algebras do exhibit this property.
However, it may not be true in general, and the categorical framework for algebra allows for functors that mix between the different components.
Still, we will use the notation $F(f) = f_1 + f_2$ in the remainder of the notes.

#definition(title: [$F$-algebra])[
  Let $CC$ be an ambient category. An $F$-algebra is a pair $(X, alpha : F(X) -> X)$, where $X in Ob(CC)$, $F$ is an endofunctor $CC -> CC$, and $alpha : F(X) -> X$.
]

This doesn't cover all of the group properties yet.
We are still missing associativity and the inverse laws.
Unfortunately, the functor $F$ primarily deals with the types of operations in an algebra, also known as the "signature", so the extra laws must be separately required.
#footnote[
  There is a different construction which generates algebras from a monad, that can encapsulate having these extra axioms, but we won't really explore that here.
  // See #link(<exc:TmonadExercise>)[Exercise].
]
For example, we will define groups as follows:

#definition-box[A group is an $F$-algebra defined by the signature $ F(X) = 1 + X + X times X $ where the components are named $[e, inv, (dot)]$, such that the following diagrams commute:

#align(center, diagram($
    X times (X times X) edge("rr", "=", sans("assoc")) edge("d", "->", (id, dot)) & & (X times X) times X edge("d", "->", (dot, id), label-side: #left) \
    X times X  edge("->", (dot), label-side: #right) & X edge("<-", (dot), label-side: #right) & X times X
$))

#align(center, diagram($
  X edge("->", (id, inv_R)) edge("d", "->", !)
  & X times X edge("<-", (inv_L, id)) edge("d", "->", (dot))
  & X edge("d", "->", !, label-side: #left) \
  1 edge("->", id, label-side: #right) & X edge("<-", id, label-side: #right) & 1 
$))

#align(center, diagram($
  1 times X edge("->", (e, id)) edge("dr", "=")
  & X times X edge("<-", (id, e)) edge("d", "->", (dot))
  & X times 1 edge("dl", "=", label-side: #left) \
  & X
$))
]

It turns out there are some interesting $F$-algebras when we consider the category of $F$-algebras themselves.
But before we get there, we must first define what it means to have a morphism of $F$-algebras.
As is standard in category theory, an $F$-algebra is simply an underlying carrier plus some extra data.
We will thus define morphisms as a function between the carrier along with proof of coherence between the data:

#definition(title: [$F$-algebra morphism])[ 
  Let $(X, alpha_X)$ and $(Y, alpha_Y)$ be two $F$-algebras in a category $CC$.
  An $F$-algebra morphism is then a morphism $f : X -> Y$ such that the following diagram commutes:

  #align(center, diagram($
    F(X) edge("->", alpha_X)
      edge("d", "->", F(f))
    & X edge("d", "->", f, label-side: #left) \
    F(Y) edge("->", alpha_Y, label-side: #right)
    & Y
  $))
] <fAlgMor>

#exercise[Verify that $F$-algebras form a category.]

Let us now interpret this commutative square in the context of the $F$-algebras generated by each of our group operations above.

- In the case of identity, the component of $F(X)$ we are focusing on is $F(X) = 1$. So both $F(X)$ and $F(Y)$ evaluate to $1$, so $F(X) -> F(Y)$ can only be the unique identity morphism in $1$.
  Thus, the left side collapses and we have a triangle:
  #align(center, diagram($
  1 edge("->", alpha_X) edge("dr", "->", alpha_Y, label-side: #right)
  & X edge("d", "->", f, label-side: #left) \ & Y$))
  Translating this to group theory, this means our choice of $alpha_Y$, the function that picks out the group identity of $Y$, must agree with the result of mapping $f$ to the group identity of $X$. 
  In other words, group homomorphisms preserve identities.
- In the case of inverse, $F(X) = X$, so we have the following diagram:
  #align(center, diagram($
    X edge("->", inv_X)
      edge("d", "->", f)
    & X edge("d", "->", f, label-side: #left) \
    Y edge("->", inv_Y, label-side: #right)
    & Y
  $))
  This translates to $inv_Y compose f = f compose inv_X$, which written algebraically says that for any $x in X$, it must hold that $f(x)^(-1) = f(x^(-1))$.
  In other words, group homomorphisms preserve inverses.
- In the case of the binary operation $(dot)$, we have $F(X) = X times X$, so we have the following diagram (recall the definition of the action of $F$ on morphisms):
  #align(center, diagram($
    X times X edge("->", (dot)_X)
      edge("d", "->", (f, f))
    & X edge("d", "->", f, label-side: #left) \
    Y times Y edge("->", (dot)_Y, label-side: #right)
    & Y
  $))
  Translating this to algebra, we have $f(x dot_X y) = f(x) dot_Y f(y)$, which is the main group homomorphism property.

As you can see, the group homomorphism properties fell purely out of just instantiating our $F$-algebra morphism law with our specific group properties.

// This also holds for many other algebraic structures:

// - 

== Initial $F$-algebras and induction

We said before that $F(X)$ builds up the input data to be used by $alpha$.
But that's a rather abstract description.
To see an example of how this is used, consider a functor $F(X) = 1 + X$.
We can define an $F$-algebra by providing an $alpha : F(X) -> X$.
Expanding the type gives us $alpha : (1 + X) -> X$, which we can define by cases:
- $alpha_1 : 1 -> X$
- $alpha_X : X -> X$

Suppose we are working with an $(X, alpha)$ that is initial in the category of $F$-algebras for $F(X) = 1 + X$.
The defining property of an initial object is that there exists a #link(<fAlgMor>)[morphism] out of this $F$-algebra to any other $F$-algebra, such that the square commutes.
This morphism is commonly known as the *catamorphism*.

For example, consider any other $F$-algebra $beta : (1 + Y) -> Y$, with corresponding $[beta_1, beta_Y]$.
Then, there exists a _unique_ $f : X -> Y$ such that this square commutes:

#align(center, diagram($
  1 + X edge("->", alpha)
    edge("d", "->", F(f))
  & X edge("d", "->", f, label-side: #left) \
  1 + Y edge("->", beta, label-side: #right)
  & Y
$))

where $F(f)$ is defined on cases:
- for the left case of the sum, there is a morphism $1_X -> 1_Y$
- for the right case of the sum, there is a morphism $X -> Y$
The square forces $f$ to respect the $F$-algebra structure.

There is a sense where the initial $(F, alpha)$ shown above represents the natural numbers $NN$, and that the unique morphism $f$ is the natural number recursor.
Recall that the natural number recursor looks something like this:

$ natrec : (y_0 : Y) -> (y_s : Y -> Y) -> (NN -> Y) $

// The $y_0$ corresponds to the $1 : 1_NN -> 1_Y$ part, where $1_NN$ is the identity element, and the $y_s$ corresponds to the $f : Y -> Y$ part.
If we change $y_0$ to be of type $1_Y -> Y$ (this is equivalent, it's just a function that ignores the input), it should be clear that the inputs $y_0$ and $y_s$ represents the two cases of $beta$.
So really, we can reframe this as: given $beta : 1 + Y -> Y$, which is the definition of the $F$-algebra you are trying to produce, you get the unique morphism $NN -> Y$ back, since it's forced by the square.

// We will not show the complete proof here, but to show that $natrec$ is a unique morphism $NN -> Y$, we must use mathematical induction.
// Roughly speaking, we would show that for the zero case, any other morphism $g : NN -> Y$ that makes the square commute would have to agree with $natrec$, and then given that $f$ and $g$ agree for some $n in NN$, they must also agree on $n + 1$.

#exercise[Prove that $natrec$ is the unique morphism that makes the above square commute.]

We defined $natrec$ for naturals here, but the idea that the unique catamorphism is the recursor holds for arbitrary $F$-algebras.

#definition(title: [Recursor])[
  Given some functor $F$, and an initial $F$-algebra $(X, alpha)$, the recursor is the unique $F$-algebra morphism to any other $F$-algebra $(Y, beta)$.
]

This generalizes to other algebra-shaped structures as well.
In fact, $F$-algebras generally build inductive data types.
For example, lists are $F(X) = 1 + A times X$ for $A$-typed lists.
The initial object in this category is then the pair $(X, alpha)$ defined by:

- $X$ is the set of all finite lists of type $A$.
- $alpha : 1 + A times X -> X$ is then defined by cases on the input:
  - In the case of $inl(star)$, just output the empty list.
  - In the case of $inr(a, x)$, output the list whose head is $a$ and tail is $x$.

#exercise[Define some other common algebraic structures using functors.]

So without initiality, what we have is only a formula for building some generic objects with this shape.
But there is nothing really forcing the objects to take a coproduct shape, or to behave well.
In fact, the initiality enforces the self-similarity of the structure map $alpha$, which we will see in the next section.

== Lambek's Theorem

There seems to be some parallel between the structure of $F(X)$ and $X$ itself.
For example, the structure map $alpha : F(X) -> X$ seemed to be perfectly split into the same cases as $X$ itself.
It turns out that this structure map itself is an isomorphism.

#theorem(title: [Lambek's theorem])[
  Given some functor $F$ and some $F$-algebra $(X, alpha)$. If $(X, alpha)$ is initial, then $alpha$ is an isomorphism.
] <lambekTheorem>

#proof[
  We begin with our structure map

  #align(center, diagram($ F(X) edge("->", alpha) & X $))

  which is initial in the category of $F$-algebras.
  Let us "use" this initiality by coming up with another $F$-algebra to map this to.
  We will use $!$ to denote the catamorphism -- the unique morphism out of the initial $F$-algebra.

  #align(center, diagram($
    F(X) edge("->", alpha) edge("d", "->", F(!)) & X edge("d", "->", !, label-side: #left) \
    ? edge("->", ?, label-side: #right) & ? \
  $))

  We will choose the particular $F$-algebra defined by applying $F$ again:
  
  #align(center, diagram($
    F(X) edge("->", alpha) edge("d", "->", F(!)) & X edge("d", "->", !, label-side: #left) \
    F(F(X)) edge("->", F(alpha), label-side: #right) & F(X) \
  $))

  If we tack on a tautological square to the bottom, we get:

  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwwLCJGKFgpIl0sWzAsMSwiRihGKFgpKSJdLFswLDIsIkYoWCkiXSxbMSwwLCJYIl0sWzEsMiwiWCJdLFsxLDEsIkYoWCkiXSxbMCwxLCJGKCEpIiwyXSxbMSwyLCJGKGFscGhhKSIsMl0sWzAsMywiYWxwaGEiXSxbMiw0LCJhbHBoYSIsMl0sWzMsNSwiISJdLFs1LDQsImFscGhhIl0sWzEsNSwiRihhbHBoYSkiXV0=
  #align(center, diagram({
  	node((0, -1), [$F(X)$])
  	node((0, 0), [$F(F(X))$])
  	node((0, 1), [$F(X)$])
  	node((1, -1), [$X$])
  	node((1, 1), [$X$])
  	node((1, 0), [$F(X)$])
  	edge((0, -1), (0, 0), [$F(!)$], label-side: right, "->")
  	edge((0, 0), (0, 1), [$F(alpha)$], label-side: right, "->")
  	edge((0, -1), (1, -1), [$alpha$], label-side: left, "->")
  	edge((0, 1), (1, 1), [$alpha$], label-side: right, "->")
  	edge((1, -1), (1, 0), [$!$], label-side: left, "->")
  	edge((1, 0), (1, 1), [$alpha$], label-side: left, "->")
  	edge((0, 0), (1, 0), [$F(alpha)$], label-side: left, "->")
  }))

  We can then "squish" the square using composition, and also using the functoriality of $F$ to simplify $F(alpha) compose F(!)$ into $F(alpha compose !)$:

  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJGKFgpIl0sWzAsMSwiRihYKSJdLFsxLDAsIlgiXSxbMSwxLCJYIl0sWzAsMiwiYWxwaGEiXSxbMSwzLCJhbHBoYSIsMl0sWzAsMSwiRihhbHBoYSBjb21wb3NlICEpIiwyXSxbMiwzLCJhbHBoYSBjb21wb3NlICEiXV0=
  #align(center, diagram({
  	node((0, 0), [$F(X)$])
  	node((0, 1), [$F(X)$])
  	node((1, 0), [$X$])
  	node((1, 1), [$X$])
  	edge((0, 0), (1, 0), [$alpha$], label-side: left, "->")
  	edge((0, 1), (1, 1), [$alpha$], label-side: right, "->")
  	edge((0, 0), (0, 1), [$F(alpha compose !)$], label-side: right, "->")
  	edge((1, 0), (1, 1), [$alpha compose !$], label-side: left, "->")
  }))

  This is exactly the #link(<fAlgMor>)[$F$-algebra morphism diagram] showing that $alpha compose !$ is a morphism from the $F$-algebra $(X, alpha)$ to itself.
  Since the morphism out of an initial object is unique, we know that it must coincide with the identity morphism, so $alpha compose ! = id_X$.
  
  This is the first half of our proof.
  It remains to be shown that $! compose alpha = id_F(X)$.
  Using the result that $alpha compose ! = id_X$, apply $F$ to both sides, getting $F(alpha compose !) = F(id_X)$, which by functoriality yields $F(alpha) compose F(!) = id_F(X)$.
  But looking at this square from above:

  #align(center, diagram($
    F(X) edge("->", alpha) edge("d", "->", F(!)) & X edge("d", "->", !, label-side: #left) \
    F(F(X)) edge("->", F(alpha), label-side: #right) & F(X) \
  $))

  We know that $F(alpha) compose F(!) = ! compose alpha$.
  Therefore, $! compose alpha = id_F(X)$, and $alpha$ is an isomorphism with inverse $!$.
]

Since $alpha$ is essentially defining the "constructors" of the inductive type defined by $F(X)$, one consequence of Lambek's theorem is that all constructors are invertible.
For example, we can derive an inverse $sans("suc")$ function that takes any $sans("suc")(n)$ and produces $n$.

#exercise[Prove that there is no non-empty initial algebra for the functor $F(X) = A times X$ in $Set$, for any arbitrary object $A$. What does this mean in English?] <noAXinitial>

#example(title: [Applying Lambek's theorem])[
  Consider the list example again, $F(X) = 1 + A times X$.
Let us derive the initial $F$-algebra using Lambek's theorem.
First, Lambek's theorem tells us that for initial algebras, $X tilde.equiv F(X)$ necessarily.
Thus, $X tilde.equiv 1 + A times X$.
Since this is a fixpoint, we can start unfolding $X$ and see what happens:

$
X &tilde.equiv 1 + A times X \
&tilde.equiv 1 + A times (1 + A times X) \
&tilde.equiv 1 + A times (1 + A times (1 + A times X)) \
&tilde.equiv dots \
&tilde.equiv 1 + (A times 1) + (A times A times 1) + (A times A times A times 1) + dots \
&tilde.equiv 1 + A + A^2 + A^3 + dots
$

This is a union of $n$-products of $A$ for all $n$, which is exactly the set of all $n$-length sequences in $A$.
]

// Another way to think about this is that the initial $F$-algebra creates a fixpoint, since it requires that $F(X) tilde.equiv X$.

// #theorem[
//   The initial $F$-algebra for the functor $F(X) = A times X$ for any set $A$ is $(emptyset, alpha)$ where $alpha$ is defined to take the $emptyset$ component of the product and return it.
// ]

// #proof[
//   By @lambekTheorem, $alpha$ must be an isomorphism, so $A times X tilde.equiv X$.
//   You may have noticed that this looks like a regular algebraic expression $a x = x$ whose only solutions are $a = 1$ or $x = 0$.
//   We can borrow this intuition for sets.

//   Given any other $F$-algebra $(Y, beta)$.
//   We must show that there exists an $F$-algebra morphism $f : (emptyset, alpha) -> (Y, beta)$ satisfying the following square:
  
//   #align(center, diagram($
//     A times emptyset edge("->", alpha)
//       edge("d", "->", (id, f))
//     & emptyset edge("d", "->", f, label-side: #left) \
//     A times Y edge("->", beta, label-side: #right)
//     & Y
//   $))

//   We can pick $f$ to be the canonical map out of the empty set.
// ]

= Coalgebra

As we know, we can get dual concepts in category theory for free by reversing the arrows.
By dualizing algebras, we get coalgebras.
Let's start with the definition and then try to extract some intuitions from it.

#definition(title: [$F$-coalgebra])[
  Let $CC$ be an ambient category. An $F$-coalgebra is a pair $(X, nu)$ where $X in Ob(CC)$, $F$ is an endofunctor $CC -> CC$ and $nu : X -> F(X)$.
]

And as usual, we must also define morphisms:

#definition(title: [$F$-coalgebra morphism])[
  Let $(X, nu_X)$ and $(Y, nu_Y)$ be two $F$-coalgebras in a category $CC$.
  An $F$-coalgebra morphism is then a morphism $f : X -> Y$ such that the following diagram commutes:

  #align(center, diagram($
    X edge("->", nu_X)
      edge("d", "->", f)
    & F(X) edge("d", "->", F(f), label-side: #left) \
    Y edge("->", nu_Y, label-side: #right)
    & F(Y)
  $))
] <fCoalgebraMorphism>

Similar to how in algebras, we had the intuition of building up some kind of "input data" to our $alpha$ morphism which then represented the constructors for our $X$, we would like to think of coalgebras as functions out of $X$, giving us some _one-step_ observation data that may involve $X$.

Let's work through an example that might solidify this intuition.
Once again, we are working temporarily in the category of sets, so let $X$ be a set.
Consider the endofunctor $F(X) = 1 + A times X$.
In algebras, this corresponds to the signature for list-y structures.

We will see now what the dual to list-y things are.
To complete the definition of an $F$-coalgebra, we need a structure map of type $nu : X -> F(X)$, which when unfolded, is $nu : X -> 1 + A times X$.
Whereas in algebras, the structure map served a purpose of consuming the structure into a single $X$, here we have $nu$ expanding the $X$ into its observable data.

Our intuition tells us that $X$ is supposed to be list-y.
So let's say our $nu$ does case analysis to see if our list is $sans("cons")$ or $sans("nil")$.
In the case of $sans("cons")$, we return $A times X$, which is the head and tail separately.
In the case of $sans("nil")$, we return $1$.
So whereas our $F$-algebra from before was building _up_ a list, now our $F$-coalgebra is essentially mapping _out_ of a list.

Compared to the algebraic version, this one sort of axiomatizes observations out of the list rather than building up the exact list structure.
We assume the list exists as a mystery object, and are able to decompose it into an element and "the rest of the stream," which continues being the mystery object.

We also have a version of Lambek's theorem for coalgebra:

#theorem(title: [Lambek's theorem for coalgebra])[
  Given some functor $F$ and some $F$-coalgebra $(X, nu)$. If $(X, nu)$ is terminal, then $nu$ is an isomorphism.
] <lambekCoalgebra>

#exercise[Prove @lambekCoalgebra.]

Of course, with coalgebraic lists, we could also imagine a situation where we have a definition that continuously returns an element of the $A times X$ side, and never returns the $1$.
In this case, the list would never end.
We cannot formulate this type using algebraically defined data (@noAXinitial), but with coalgebraically defined codata, this is completely in bounds.
In fact, we may even specify that the stream _cannot_ ever end.
In this case, we only need to use signature functor $F(X) = A times X$, opting not to include the extra $1$.
This is useful for reasoning about applications such as servers which are designed to run and continue responding to input forever.
In the next section we will discuss the terminal $F$-coalgebra and coinduction.

== Coinduction and bisimulation

Recall that a terminal object has morphisms into it from every other object.
These morphisms are typically called *anamorphisms*.
To see an example, let's work in $Set$ again, with the stream functor, where $F(X) = A times X$, for some type $A$.
This represents streams of elements with type $A$.

We can use @lambekCoalgebra to derive what the terminal coalgebra should look like.
Starting with $X tilde.equiv A times X$, we can unfold several times to get $X tilde.equiv A times A times A times dots$.
This is an unending product of $A$ by itself, which is the same as the function space $NN -> A$.
We can also write this as $A^NN$, using exponential notation for functions.

Next is to define the structure map, $nu_X : X -> A times X$.
Of course, we don't really have a choice in this matter either -- it must follow from the terminality conditions.
An obvious choice would be to just pick the head and tail and return that as a pair.

#definition[The structure map for the terminal $F$-coalgebra defined by $F(X) = A times X$ is $ nu_X &: X -> A times X \ nu_X ((a_0, a_1, a_2, dots)) &= a_0, (a_1, a_2, dots)  $] <reassociateHeadTail>

But does this choice work?
We must check that all the rules are satisfied.

#lemma[
  For any $F$-coalgebra $(Y, nu_Y)$, there exists a morphism $f : (Y, nu_Y) -> (X, nu_X)$.
] <fExists>

#proof[
  First, we must show that for any $(Y, nu_Y)$, that an $f : Y -> X$ even exists.
We will do so by generating a sequence of $a$'s from $nu_Y$.
First, begin with $y in Y$, and run $nu_Y (y)$ to get $y_1 : A times Y$.
We'll take the first element $head(y_1) : A$ as the first observation, and keep the rest which is $tail(y_1) : Y$.
Then, we can repeat the process, running $nu_Y (y_1)$ to get $y_2 : A times Y$.
By continuing to repeat this process, we'll just end up with an infinite series of $a$'s, which we can write as $a_0, a_1, a_2, dots$.
We'll refer to this as the _behavior_ of $Y$.
Notice that we didn't need to depend on what the structure of $Y$ was.

Now we need to verify that our choice of $f$ is well-behaved, with regards to all of the conditions we defined earlier.
Let us revisit the commuting square from @fCoalgebraMorphism:
#align(center, diagram($
  Y edge("->", nu_Y)
    edge("d", "->", f)
  & A times Y edge("d", "->", F(f), label-side: #left) \
  A^NN edge("->", nu_X, label-side: #right)
  & A times A^NN
$))

Translating this to an equation, we get:

$ nu_X compose f = F(f) compose nu_Y $

First, note that it is necessary that $F(f) = id times f$.
This is because of the functoriality of $F$, similar to how our $F$s earlier had to be a coproduct.
So really, we have:

$ nu_X compose f = (id times f) compose nu_Y $

This requires us to show that $nu_Y$ indeed produces the head element of the list that we are manipulating in $nu_X$.
More literally, if we have $y in Y$, then $f(tail(nu_Y (y)))$ must produce the same thing as just taking the tail end of $f(y)$.
This is just true by definition.
To spell it out with elements, we have:

$ nu_X (f(y)) &= (id times f) ( nu_Y (y)) \ 
nu_X ((a_0, a_1, a_2, dots)) &= \
a_0, (a_1, a_2, dots) &= \
&= (id times f) ( nu_Y (y)) \
&= (id times f) (a_0, y_1) \
&= a_0, f(y_1) \
$

As noted above, $y_1$ is just the next sequence after $y$, so it will produce $a_1, a_2, dots$ by $f$.
So this commuting square checks out.
]

#lemma[The morphism $f$ defined in @fExists is unique.] <fUnique>

For this, we'll need to use a different kind of reasoning than before.
We will have to use *coinduction*, which is dual to induction and is perfect for working with codata such as streams.

#proof[
  Suppose we have $g : Y -> A^NN$ that respects the square.
We would like to show that $f = g$.
Extensionally, this means $f$ and $g$ produce the same output on all inputs, as functions.
Now, $g$ is an unknown function, but it has the shape $Y -> A^NN$, so we know it produces an infinite stream of $a$'s.
Furthemore, we know that:
#align(center, diagram($
  Y edge("->", nu_Y)
    edge("d", "->", g)
  & A times Y edge("d", "->", id times g, label-side: #left) \
  A^NN edge("->", nu_X, label-side: #right)
  & A times A^NN
$))
which says that $nu_X compose g = (id times g) compose nu_Y$.
This means at least the first element of the sequence produced by $g$ must be picked out by $nu_Y$.
Otherwise, $id(head(nu_Y (y)))$ would not produce the same result as $head(nu_X (g(y)))$.
Thus, the first element of the sequence must be $head(nu_Y (y))$.

Then, regarding the tail end of the sequence, we would like to argue coinductively that it must follow the same shape.
Specifically, let $nu_Y (y) = (a_0, y')$.
Following the top-right path, we can see that the tail part of the result is $g(y')$.
Since $g$ is unknown, we can't really say what this is yet, but we can look at the left-bottom path, which tells us that the tail part of the result must be $tail(g(y))$, since as a reminder, our $nu_X$ specifically splits a sequence $A^NN$ into its $head$ and $tail$ parts.
This tells us that $g(y') = tail(g(y))$, which is exactly what we expect.

So putting this together with $f$, we know that both $head(f(y))$ and $head(g(y))$ result in $fst(nu_Y (y))$.
So $f(y)$ and $g(y)$ agree on that part.
For the tail segment, we know that $tail(g(y)) = g(y')$.
It turns out this is also true of $f$, due to how we defined it: $tail(f(y)) = f(y')$.
Thus, to determine if $tail(f(y)) = tail(g(y))$, it suffices to show that $f(y') = g(y')$.
But since $y'$ is exactly self-similar to $y$, by coinduction, we know that $f(y') = g(y')$.
]

In the above proof, we used function extensionality to show that $f$ and $g$ are equal.
But for showing two coalgebra are "the same," it is often more convenient to use a weaker notion of equivalence.
A classic example is of automata, which we will see more about in a later section.
It is completely sensical to have two automata that capture the same language (yielding the same transitions), yet have different non-reconcilable states.
For this, we will introduce bisimulation.

#definition(title: [Bisimulation of streams])[
  Let $(X, nu_X)$ and $(Y, nu_Y)$ be $F$-coalgebras, where $F(X) = A times X$.
  Let $R$ be a relation between $X$ and $Y$ -- specifically, $R subset X times Y$.
  $R$ is a *bisimulation* iff for any $(x, y) in R$:

  $ head(x) = head(y) and (tail(x), tail(y)) in R $
] <bisimulationOfStreams>

Then, it is said that $X$ and $Y$ are *bisimilar*.
This sort of looks like a more generalized version of the reasoning we did as a part of the uniqueness proof, but with equality replaced with the relation $R$.
But the reasoning is still stream-specific, and relatively ad-hoc.
We'd like to not have to make arbitrary bisimulation conditions for every type we'd like to analyze.

It turns out if we just take everything that has specifically to do with streams and abstract it, we can arrive at a more general notion of bisimulation.


#definition(title: [Aczel-Mendler bisimulation])[
  Let $CC$ be a category with products, and $F : CC -> CC$ be an endofunctor.
  Let $(X, nu_X)$ and $(Y, nu_Y)$ be $F$-coalgebras.
  Let $R$ be a subobject of the product object $X times Y$ with projection morphisms $pi_X$ and $pi_Y$ such that there exists a morphism $nu_R : R -> F(R)$ such that the following diagram commutes:

  // https://q.uiver.app/#r=typst&q=WzAsNixbMSwwLCJSIl0sWzAsMCwiWCJdLFsyLDAsIlkiXSxbMSwxLCJGKFIpIl0sWzIsMSwiRihZKSJdLFswLDEsIkYoWCkiXSxbMyw1LCJGKHBpXzEpIl0sWzMsNCwiRihwaV8yKSIsMl0sWzAsMSwicGlfMSIsMl0sWzAsMiwicGlfMiJdLFsyLDQsIm51X1kiXSxbMCwzLCJudV9SIiwxXSxbMSw1LCJudV9YIiwyXV0=
#align(center, diagram({
	node((0, 0), [$R$])
	node((-1, 0), [$X$])
	node((1, 0), [$Y$])
	node((0, 1), [$F(R)$])
	node((1, 1), [$F(Y)$])
	node((-1, 1), [$F(X)$])
	edge((0, 1), (-1, 1), [$F(pi_1)$], label-side: left, "->")
	edge((0, 1), (1, 1), [$F(pi_2)$], label-side: right, "->")
	edge((0, 0), (-1, 0), [$pi_1$], label-side: right, "->")
	edge((0, 0), (1, 0), [$pi_2$], label-side: left, "->")
	edge((1, 0), (1, 1), [$nu_Y$], label-side: left, "->")
	edge((0, 0), (0, 1), [$nu_R$], label-side: left, "->")
	edge((-1, 0), (-1, 1), [$nu_X$], label-side: right, "->")
}))
] <genericBisimulation>

Let's quickly make sense of this in the context of our previous @bisimulationOfStreams again.
We have some relation $R$ which is a subobject of the product.
This corresponds exactly with $R subset X times Y$.
The rough interpretation of this is that at the current state, $X$ and $Y$ are related through $R$.

Then, we have the object $F(R)$, which is a lift of the product through $F$.
So for streams, since $F(X) = A times X$, we have $F(R) subset (A times X) times (A times Y)$.
Notice how this part is completely determined by the specific $F$'s interaction with the relation.
The $nu_R$ lifting operation simply calls $head$ and $tail$ component-wise on both the left and right sides.
Then, the $F(pi_1)$ projection operator would grab the components separately and turn them into a product, and $F(pi_2)$ does the corresponding thing for $F(Y)$.

The commuting squares, like earlier, essentially force us to take this component-wise motion.

// This leads us to 

#exercise[Does the category of $F$-algebras have an initial object for any $F$? Does the category of $F$-coalgebras have a terminal object for any $F$?]

// = Applications of coalgebra

= Automata

We have been working a lot with streams so far, so from here on we will be introducing some richer coalgebras that have applications in other fields.
Automata are a classic example of coalgebras in practice.
At a high level, an automaton is a state machine that has states and transitions between them.
It has a notion of "accept" states which allow the machine to respond with a success response.
This is often used in recognizing languages, such as in parsing for compiler development, but also for network protocols and hardware state machines. 

We'll look at how automata can be abstracted using algebras and coalgebras, and then work through a generalization of Brzozowski's minimization algorithm using our definition, in order to see how to use the duality of algebras and coalgebras in order to achieve minimization.
Let's start with a formal definition of automata.

#definition(title: [Deterministic automaton])[
  For some alphabet $Sigma$, a *deterministic automaton (DA)* is a 4-tuple $(Q, delta, i, F)$:
  - $Q$, a set of states
  - $delta : Q times Sigma -> Q$, a transition map
  - $i in Q$, an initial state
  - $F subset.eq Q$, final states
]

Visually, we can represent an automaton like this:

#align(center, diagram(
	node-stroke: .1em,
	// node-fill: gradient.radial(blue.lighten(80%), blue, center: (30%, 20%), radius: 80%),
	spacing: 4em,
	edge((-1,0), "r", "-|>", `start`, label-pos: 0, label-side: center),
	node((0,0), $q_0$, radius: 2em),
	edge(`b`, "-|>"),
	node((1,0), $q_1$, radius: 2em),
	edge(`c`, "-|>"),
	node((2,0), $q_2$, radius: 2em, extrude: (-2.5, 0)),
	edge((1,0), (1,0), `b`, "-|>", bend: 130deg),
	edge((0,0), (2,0), `a`, "-|>", bend: -40deg),
))

This visualization represents the formal automaton defined as $({q_0, q_1, q_2}, {#`a`, #`b`, #`c`}, delta, q_0, {q_2})$ where $delta$ would map:
- $(#`a`, q_0) mapsto q_2$
- $(#`b`, q_0) mapsto q_1$
- $(#`b`, q_1) mapsto q_1$
- $(#`c`, q_1) mapsto q_2$
- all other combinations of states would resolve to an implicit "error" state (which would also be in $Q$), which only has transitions back to itself.
  It does not appear in $F$, the set of final states.
  For all intents and purposes in these notes, we can safely just ignore the fact that it exists, although we should formally make a mental note of the erroring behavior, since $delta$ is not a partial function.

The double-circle means that $q_2$ is a final state, in other words, that $q_2 in F$.
This automaton will recognize a language consisting of either the exact string `a` or any non-zero number of `b`s followed by a `c`.
This is typically written using the terse regular expression syntax as `a|(b+)c`.

#let LL = $cal(L)$
Formally, a language $LL$ is just a series of strings consisting of symbols in the alphabet $Sigma$.
An automaton *recognizes* a language if for every string $s$ in the language, running $s$ through the automaton would result in a final state.

There is also a variant which allows non-deterministic transitions -- for example, it would be allowed to have multiple arrows from the same state with the same transition.
This machine is known as a _non-deterministic_ automaton.

#definition(title: [Non-deterministic automaton])[
  For some alphabet $Sigma$, a *non-deterministic automaton* is a 4-tuple $(Q, delta, i, F)$:
  - $Q$, a set of states
  - #rect[$delta : Q times Sigma -> cal(P)(Q)$, a transition map]
  - $i in Q$, an initial state
  - $F subset.eq Q$, final states
]

The $delta$ is the only difference from the DA definition.
Instead of only transitioning to one state, it could possibly transition to any number of states.
A non-deterministic automata would accept a string from a language if taking any path using the symbols of the string would result in acceptance.

Traditionally, non-deterministic automata would be converted deterministic using an algorithm such as the powerset construction, in which you would consider the set of all states that could possibly result following a particular transition.
There are also some methods of evaluating non-deterministic automata directly without first doing the conversion, as the conversion may produce an explosion ($O(2^n)$) of states in the resulting DA.

For this section, we will consider a particular problem concerning automata: there is a sense in which an NFA might not be minimal.
For example, consider this automaton:

#align(center, diagram(
	node-stroke: .1em,
	spacing: 4em, {
	// edge((-1,0), "r", "-|>", `start`, label-pos: 0, label-side: center)
	node((rel: (1,0)), $q_0$, radius: 2em, extrude: (-2.5, 0))
	edge(`a`, "-|>")
	node((rel: (1,0)), $q_1$, radius: 2em)
	edge(`a`, "-|>")
	node((rel: (1,0)), $q_2$, radius: 2em)
	edge(`a`, "-|>")
	node((rel: (1,0)), $q_3$, radius: 2em)
	edge((4,0), (1,0), `a`, "-|>", bend: -30deg)
}))

You could easily imagine collapsing all of these down to a single node.
Due to this, there are several minimization algorithms.
A well-known algorithm, due to Brzozowski, involves reversing the NFA, determinizing it using the powerset construction, and then reversing it again.
In this next section, we will investigate a category-theoretic approach by @bonchiAlgebracoalgebraDualityBrzozowskis2014 to show why this works, specifically for the case of deterministic automata.

== The category of automata

In order to categorify automata, we must first identify a category.
We want the objects to be automata, so we must define some morphisms.

#definition(title: [Automaton morphism])[
  For some alphabet $Sigma$, a morphism between two automata $(Q_1, delta_1, i_1, F_1)$ and $(Q_2, delta_2, i_2, F_2)$ is defined as a function $f : Q_1 -> Q_2$ such that the following hold:

  - $f$ commutes with the transition map, or in other words, for any $s in Sigma$, this square commutes:
    #align(center, diagram($
      Q_1 edge("->", f)
      edge("d", "->", delta_1 (-, s))
      & Q_2 edge("d", "->", delta_2 (-, s), label-side: #left) \
      Q_1 edge("->", f, label-side: #right)
      & Q_2
    $))
  - $f$ preserves the initial state, or in other words $f(i_1) = i_2$
  - $f$ preserves the final states, or in other words $f(q) in F_2$ for all $q in F_1$

  // This definition is analogous for both deterministic and non-deterministic automata.
] <automatonMorphism>

Thus, we can form a category of DAs:

#definition(title: [Category of deterministic automata, $DA_LL$])[
  For some alphabet $Sigma$ and language over that alphabet $LL$, the category $DA_LL$ is defined as a category where:
  - objects are DAs that recognize the language $LL$
  - morphisms are defined as in @automatonMorphism
]

It's important that the category itself is parameterized by a language $LL$, since morphisms need to preserve the language.
If this was not the case, then we could not have initial or final objects at all -- it would essentially require that all automata at all recognize the same language, which is not the case.
Such a category would still exist, and in fact $DA_LL$ is a subcategory of that category, but it is not useful to us.

#remark[
  We can characterize a DA categorically as _both_ and algebra and as a coalgebra.
  As an algebra, it uses the signature functor
  
    $ F(Q) = 1 + Sigma times Q $

  In order to represent an automata as an algebra, we would need a structure map of type $alpha : 1 + Sigma times Q -> Q$.
  The $1 -> Q$ part represents the initial state, since it takes no input, and $Sigma times Q -> Q$ is the type of a transition map -- it takes a transition symbol, a state, and outputs the next state.
  
  As a coalgebra, it can be characterized with the signature functor:
  
    $ F(Q) = 2 times Q^Sigma $
  
  
  For the coalgebra case, we need a structure map $nu : Q -> 2 times Q^Sigma$.
  For any input state $q in Q$, the $Q^Sigma$ part of the output represents all possible states that the input state could transition to, and $2$ refers to a tag on each state that is assigned the value $1$ if that state is a final state, or the value $0$ if it isn't.
]

== Minimality of automata

Next, let us consider the initial and terminal objects of $DA_LL$.
We'd like to determine some automaton that recognizes $LL$ and has a morphism to every other automaton.
A pretty trivial "maximal" object that lets us do this is to add every single possible word as a state.

Formally, let's define this automaton:

#definition(title: [Initial object of $DA_LL$])[
 Define the initial automaton $Init$ as: 
- $Q_Init$ is defined as $Sigma^*$, the set of all strings over the alphabet $Sigma$
- $delta_Init : Q times Sigma -> Q$ simply concatenates the currently running state's string with the transition symbol
- $i_Init$ is the state corresponding to the empty string
- $F_Init$ are the states corresponding to all strings in $LL$
]

Of course, we must show that it is in fact initial.

#theorem[The automaton described above is initial in $DA_LL$.]

#proof[
  Consider some other automaton $(Q', delta', i', F')$.
  We must define a morphism from $Init$ to this automaton.

  First, define $f : Q_Init -> Q'$.
  For every state $q in Q_Init$, there is a corresponding string $s in Sigma^*$. We will define $f$ to map $s$ to a state in $Q'$ by running $Q'$ -- in other words, starting with $i'$ and transforming it using $delta'$ on each symbol of $s$, and then returning the final state that it landed in.

  We must show that $f$ commutes with the transition map, or in other words, for any symbol $t in Sigma$: $ f compose delta_Init (-, t) = delta' (-, t) compose f $
  Let $q in Q_Init$ be an arbitrary state in $Init$, and $s in Sigma^*$ be the corresponding string.
  Then, we are trying to show that $f(delta_Init (q, t)) = delta'(f(q), t)$.
  Since $delta_Init$ is defined by concatenation, we have $f(delta_Init (q, t)) = f(s + t)$ on the left side.
  Since $f$ simply runs $delta'$ iteratively, this is actually true _by the definition_ of $f$.

  It is trivial to show that $f$ also preserves the initial and final states.

  In order to show $f$ is the unique such morphism, assume $g : Q_Init -> Q'$.
  We need to show for any state $q$, that $f(q) = g(q)$.
  Since the states map one-to-one with all strings $Sigma^*$, perform induction on strings.
  For the empty string, the corresponding state is the initial state, which is preserved by the requirement of the automaton morphism.
  Thus, $f(i_Init) = g(i_Init) = i'$.

  For the inductive case, assume $f(q) = g(q)$. Then, for any symbol $t in Sigma$, identify the state corresponding to concatenating $s + t$ (once again letting $s$ be the string corresponding to $q$).
  We must show $f(s + t) = g(s + t)$.
  By the commutative square, we can rewrite this property to $delta'(f(q), t) = delta'(g(q), t)$.
  Since $f(q) = g(q)$ by our inductive hypothesis, the two sides are identical.
]

#proof(title: [Alternate proof])[
  Note that automata behave algebraically.
  Use @lambekTheorem to deduce that the structure map $1 + Sigma times Q -> Q$ must be an isomorphism, so:

  $ Q tilde.equiv 1 + Sigma times Q $

  Expanding this, we get: $Q tilde.equiv 1 + Sigma times (1 + Sigma times (1 + Sigma times dots))$, which simplifies to $1 + Sigma + Sigma^2 + Sigma^3 dots$.
  This is exactly $Sigma^*$ -- all strings of all lengths, sourced from the alphabet.
  #footnote[ 
  In fact, this approach can be used to derive the initial automaton.
  I didn't realize this until after I wrote the previous proof...
  However, I left the original proof in, because it actually defines the function needed for the morphism. 
  ]
]


The rough design of this morphism is that for some arbitrary automaton $Q$, we're running every possible string in $Sigma^*$ to see which states are able to be reached via $Q$, and capturing that in a single function $f$.

We're interested specifically in automata where every state is reachable.
This means there's no redundancies in the states -- if you had some redundant state that isn't final, then only running $delta$ until completion would completely miss that state, excluding it from the image of the morphism out of the initial automaton.
We capture this with the following definition:

#definition(title: [Reachable automaton])[
  An automaton $Q$ is *reachable* if the unique morphism out of the initial automaton $Init -> Q$ is an epimorphism.
] <reachableAutomaton>

In sets, epimorphisms (set functions) capture the notion of surjectivity, which means every element of the codomain has a pre-image.
Since automata are essentially sets with more structure, a morphism being epic captures the same notion, which in automata corresponds to every state being reached by a morphism.
If this property is true of the morphism out of the initial automaton (which remember, runs every possible string through the automaton), we know every state is being used, which captures our desired property of reachability.

There is a similar construction on the coalgebraic side.
We can imagine a terminal automaton, which has morphisms going into it from any other automaton.
For some arbitrary automaton $Q$, we'd imagine that the result of a morphism should be some _observation_ of the states in $Q$.
So the terminal automaton should be a collective observation about all possible automata in $DA_LL$.

#definition(title: [Terminal object in $DA_LL$])[
  The terminal automaton $Term$ is defined as:
  - $Q_Term$ is the set of all possible subsets of $Sigma^*$. This represents all languages that could possibly be recognized for this alphabet.
  - $delta_Term : Q times Sigma -> Q$ maps every $(q, s) in Q times Sigma$ to the state representing the remainder of the language after consuming the prefix $s$.
    This is also known as the _Brzozowski derivative_.
  - $i_Term$ is the language $LL$.
  - $F_Term$ is the set of all languages that contain the empty string $epsilon.alt$.
]

Staring at this definition, it may kind of make sense why this could capture all observations, but let's make this concrete by actually proving terminality.

#theorem[The automaton described above is final in $DA_LL$.]

#proof[This proof largely follows in the same vein as the initial object proof.
As such, we will skip some parts of it for brevity. Just trust me #emoji.face.wink.

Consider some other automaton $(Q', delta', i', F')$.
We'll now define $f : Q' -> Q_Term$.
For any state $q in Q'$, we will consider the automaton that has the same states and transitions as $Q'$, but with initial state $q$.
The language that this automaton recognizes will be a set of a strings, which is a subset of $2^Sigma^*$.
This language is the output of $f$.

The exercise of verifying that $f$ preserves the initial and final states as well as the transition map is left to the reader.
]

#exercise[Verify that $f$ satisfies the requirements for being a $DA_LL$-morphism.]

#proof(title: [Alternative proof])[
  Same as before, notice that $DA_LL$ is coalgebraic and use @lambekCoalgebra.
  The structure map $nu : Q -> 2 times Q^Sigma$ must be an isomorphism, so:

  $ Q tilde.equiv 2 times Q^Sigma $

  Expanding this, we get $
  Q &tilde.equiv 2 times (2 times (2 times (dots)^Sigma)^Sigma)^Sigma \
  &= 2 times 2^Sigma times (2 times (dots)^Sigma)^Sigma^2 \
  &= 2 times 2^Sigma times 2^Sigma^2 times (dots)^Sigma^3 \
  &= 2 times 2^Sigma times 2^Sigma^2 times 2^Sigma^3 times dots \
  &= 2^(1 + Sigma + Sigma^2 + Sigma^3 + dots) \
  &= 2^Sigma^*
  $

  Thus, $2^Sigma^*$ is the state space for the terminal automaton.
]

The rough design for this morphism is that we're mapping the automaton to what language it recognizes, inside of $Term$.
In that sense, this morphism would capture the behavior of all the strings that could possibly be recognized by the automaton.

This captures another important property, which is that every state is distinct.
Without this property, you could have two states which recognize the same suffix language.
That wouldn't be very minimal.
For minimality, we care specifically that there are no duplicate states that can just be merged.
This can be captured by the definition of observability, which is dual to @reachableAutomaton:

#definition(title: [Observable automaton])[
  An automaton $Q$ is *observable* if the unique morphism into the terminal automaton $Q -> Term$ is a monomorphism.
] <observableAutomaton>

Again, to make a comparison to sets, a set function is monic if it is injective, or that distinct inputs map to distinct outputs.
Thus, a morphism in $DA_LL$ is monic if it maps distinct input states to distinct output states.
If our output state is the terminal automaton, then two states mapping into the same output state means that they recognized the same language, which would mean they were duplicated.

Putting these together, we can finally define what a minimal automaton is:

#definition(title: [Minimal automaton])[
  An automaton $Q$ is *minimal* if it is both #link(<reachableAutomaton>)[reachable] and #link(<observableAutomaton>)[observable].
] <minimalAutomaton>

The reachability property enforces that no states can be deleted, and the observability property enforces that no states can be merged, at least without changing the language being recognized.
These are the only two ways to reduce an automaton without changing the language.
This claim could be justified by the fact that the definition of minimization used above coincides with the minimization definition for a coalgebra defined through epi-mono factorization @bezhanishviliMinimizationDuality2012.

On the computation side of things, reachability is pretty trivial to compute algorithmically -- just traverse the state machine and grab all the states visited.
On the other hand, observability requires quotienting by equivalence classes of a hard-to-compute property of basically _every_ state.
In practice, algorithms such as Hopcroft's algorithm optimize this by incrementally comparing states and quotienting as you go.

== Reversing automata

The crux of Brzozowski's minimization algorithm involves reversing the automaton.
The intuition here is, if reachability is more straightforward, we should aim to do it.
Then, we can find some dualization property that allows us to somehow transfer reachability of an automaton into observability of the reverse language, and then use reachability _again_ to get both desired properties on the same language.

The actual reversal process amounts to reversing the arrows of the transition map, as well as exchanging the initial and final states.
Note that normally, when you do this to a deterministic automaton, it becomes a _non-deterministic_ one.
This is because there could be multiple final states, but only one initial state.
When you reverse it, you have a number of initial states.
The algorithm requires that you then make the non-deterministic automaton deterministic, through the powerset construction.

We'll explore a construction which combines the reversing and powersetting in one go.
First off, consider what the shape of output we want is, since this will guide our type-checking as we hone in towards a solution.
We are starting off with a category $DA_LL$ of deterministic automata, and we are trying to get some way of taking each object and obtaining the reverse automata.

Notice that the reverse automata will necessarily recognize the reverse language.
So the output will be an automaton which recognizes $rev(LL)$, in other words an object in $DA_rev(LL)$!
This makes it necessary for us to provide a _functor_ with this signature:

$ DA_LL -> DA_rev(LL) $

As always, we need to find a functor, because the rules governing morphisms will restrict the way the objects can even be mapped to only well-behaved maps.
Otherwise, we could produce some degenerate maps.
This will also give us more benefits, as we will see later.

Time to define action on objects.
For some arbitrary object $Q in DA_LL$, we'd like to produce the reverse automaton.
We can start with what we expect $delta_Q'$, the $delta$ of the transformed automaton to be.
It should be some sort of reversing function, so we should be taking the pre-image of $delta_Q$:

$ delta_Q' :equiv (q, s) mapsto {q' in Q | delta(q', s) = q} $

But this doesn't type-check.
The result is a set, since multiple $q'$s could map to the same $q$ under the old $delta$.
This means our state space fundamentally needs to be a powerset of $Q$.
In that case, $delta_Q'$'s type would need to be $PP(Q) times Sigma -> PP(Q)$.
We can update the function to look like this:

$ delta_Q' :equiv (q, s) mapsto {q' in Q | delta(q', s) in q} $ <preImageDelta>

We can essentially fill in the rest of the definitions now:

- $Q'$'s state space is $PP(Q)$
- $delta_Q'$ was defined above
- $i_Q'$ is the set containing all the final states in $Q$
- $F_Q'$ is the set containing the initial state in $Q$

Here is where the magic happens.
The function $delta_Q$ is essentially a function over sets.
Even though it's doing $Q times Sigma -> Q$, this is equivalent to $Q -> (Sigma -> Q)$, which is $Q -> Q^Sigma$.
Over in our reverse language, we have $delta_Q'$ having type $PP(Q) times Sigma -> PP(Q)$, which is the same as $PP(Q) -> PP(Q)^Sigma$.

*This is exactly the behavior of the contravariant power functor!*

Let's step back one step and build up to this insight.
If we just considered the category of sets $Set$, the _powerset functor_ $PP : Set -> Set$ maps every set $X$ to its power set $PP(X)$.
In particular, for morphisms, it has type $PP(X ->^f Y) : PP(X) -> PP(Y)$.
For any subset of $X$, it maps $f$ restricted to that subset to obtain an image that is in the subset of $Y$.

There is also a contravariant version, which we will denote $PP^* : opp(Set) -> Set$.
In particular, the action on morphisms has type $PP^* (X ->^f Y) : PP(Y) -> PP(X)$.
This action maps a subset of $Y$ into the _pre-image_ under $f$, which is a subset of $X$.

This is exactly what our $delta_Q'$ is doing!
In essence, our desired transformation is performing the covariant powerset functor on each of the components of the automata.
We can concretize this idea by constructing a forgetful functor $U : DA_LL -> Set$ which simply takes the set of states and forgets all the other structure.
Then, we can see clearly that:

$ U(Q) ->^PP^* U(Q') $

Here we introduce a powerful property of the contravariant powerset functor:

#lemma[The contravariant powerset functor $PP^*$ is left adjoint to its own opposite functor $opp(PP^*)$.] <contrPowerSetSelfDual>

#proof[
  The contravariant powerset functor is $PP^* : opp(Set) -> Set$.
  Its opposite functor would be $opp(PP^*) : Set -> opp(Set)$.
  This amounts to showing that for any $X, Y in Set$:

  $ Hom_(Set) (PP^* (X), Y) &tilde.equiv Hom_Set (X, opp(PP^*)(Y)) \ 
  Hom_Set (Y, PP^*(X)) &tilde.equiv Hom_Set (X, opp(PP^*)(Y))
  $

  and really, both $PP^*$ and $op(PP^*)$ have the same action on sets, which is to turn them into their power sets. So really, we are trying to show:

  $ Hom(Y, PP(X)) &tilde.equiv Hom(X, PP(Y)) $

  We can show this via creating a bijection.
  First, the forward direction: define $fwd : Hom(Y, PP(X)) -> Hom(X, PP(Y))$ with the function $lambda (f : Y -> PP(X)) . lambda (x : X) . {y in Y | x in f(y)}$.
  #footnote[Sorry about the sudden lambda notation, I needed to see the type of the argument inline for a second...]
  
  Then, define the inverse direction $bwd : Hom(X, PP(Y)) -> Hom(Y, PP(X))$ with the function $lambda (g : X -> PP(Y)) . lambda (y : Y) . {x in X | y in g(x)}$.

  It's easily to show the inverses compose to the identity:

  $ forall f . " " f & = bwd(fwd(f)) \ 
  & = lambda (y : Y) . {x in X | y in fwd(f)(x) } \
  & = lambda (y : Y) . {x in X | y in (lambda (x : X) . { y in Y | x in f(y)})(x) } \
  & = lambda (y : Y) . {x in X | y in { y in Y | x in f(y) } } \
  & = lambda (y : Y) . {x in X | x in f(y) } } \
  & = lambda (y : Y) . f(y) } } \
  & = f \
  $

  and the other way:

  $ forall g . " " g &= fwd(bwd(g)) \
  & = lambda (x : X) . {y in Y | x in bwd(g)(y) } \
  & = lambda (x : X) . {y in Y | x in (lambda (y : Y) . {x in X | y in g(x) })(y) } \
  & = lambda (x : X) . {y in Y | x in {x in X | y in g(x) } } \
  & = lambda (x : X) . {y in Y | y in g(x) } \
  & = lambda (x : X) . g(x) \
  & = g \
  $
]

@contrPowerSetSelfDual is essentially saying that the contravariant powerset functor is self-dual.
The strategy now is: if we can somehow lift this self-duality into $DA_LL$, we will be able to get an operation that turns reachable automata into observable automata and vice versa.

#let F2 = $overline(2)$

We will devise a functor called $F2$, which is self-dual, that makes this diagram commute:

#align(center, diagram($
  DA_LL
  edge("-->", F2, label-side: #left, bend: #(15deg))
  edge(stroke: #0pt, tack.t, label-side: #center)
  edge("<--", opp(F2), label-side: #right, bend: #(-15deg))
  edge("d", "->", U)
  & opp(DA_rev(LL)) edge("d", "->", U, label-side: #left) \
  Set
  edge("->", PP^*, label-side: #left, bend: #(15deg))
  edge(stroke: #0pt, tack.t, label-side: #center)
  edge("<-", opp(PP^*), label-side: #right, bend: #(-15deg))
  & opp(Set)
$))

This essentially lifts the self-duality of $PP^*$ into $DA_LL$.
The paper @bonchiAlgebracoalgebraDualityBrzozowskis2014 notes that this lifting is true generically

#definition(title: [Self-dual powerset functor lift])[
  Define the functor $F2 : DA_LL -> opp(DA_rev(LL))$ as:

  - action on objects: $F2(Q)$ applies the contravariant powerset functor to all components of the automaton:
    - $Q$ is transformed into the power set of states $PP(Q)$
    - $delta_Q$ is transformed into the pre-image map as described in @preImageDelta. Note that this recognizes the reverse language.
    - $i_Q$ is transformed into the set of all final states
    - $F_Q$ is transformed into the set of all initial states
  - action on morphisms maps a morphism $Q_1 ->^f Q_2$ to its inverse mapping $PP(Q_2) ->^(overline(PP)(f)) PP(Q_1)$
] <F2Def>

#proof[ 
  Omitting for brevity.
  See #cite(<bonchiAlgebracoalgebraDualityBrzozowskis2014>, supplement: [Proposition 9.1]) for the full proof.
]

== (Co-)reflective subcategories

In order to see how all of this machinery comes together, we will introduce some subcategories of $DA_LL$:
- $rDA_LL$ is the category of _only_ reachable automata in $DA_LL$
- $oDA_LL$ is the category of _only_ observable automata in $DA_LL$
- $mDA_LL$ is the category of _only_ minimal automata in $DA_LL$

Since minimal automata are ones that are both reachable and observable, it must also be true that $mDA_LL$ is a subcategory of both $rDA_LL$ and $oDA_LL$.
This means the subcategory relationships can be represented as a sort of diamond diagram:

#align(center, diagram($
& DA_LL
edge("dl", "<-hook")
edge("dr", "<-hook") \
rDA_LL edge("dr", "<-hook") & & oDA_LL edge("dl", "<-hook") \
& mDA_LL
$))

The arrows between them represent inclusion functors.
In fact, these are a special kind of subcategory known as a _reflective_ (and _co-reflective_) subcategory.
For reflective subcategories, this means that the inclusion functor has a left adjoint.
Dually, for co-reflective subcategories, this means that the inclusion functor has a right adjoint.
Let us see why this holds.

#theorem[$rDA_LL$ is a co-reflective subcategory of $DA_LL$. In other words, supposing $I : rDA_LL arrow.r.hook DA_LL$ is the inclusion functor, there exists a functor $R : DA_LL -> rDA_LL$ such that $ I tack.l R $] <rDALCoreflectiveSubcategory>

#proof[
  // #TODO
  // Following @jiri_adamek_abstract_2009.
  For our action on objects, assume we are dealing with an object $Q : DA_LL$.
  We are looking to construct a functor $R$ that is right-adjoint to $I$.

  #let eps = $epsilon.alt$
  
  To do this, we must first define $R$, then construct a unit $eta : id_rDA_LL => R compose I$ and a counit $eps : I compose R => id_DA_LL$ that satisfies the triangle inequalities below.
  Since we are looking for a functor that takes an automaton with possibly unreachable states into its closest reachable approximation, the most obvious thing to do is simply discarding all unreachable states.
  Using the machinery we used above to define reachability, we can say that $R(Q)$ takes the codomain of the morphism $Init -> Q$.
  Thus, $R$ is obviously reachable, and lies in $rDA_LL$.

  Next, define the unit: for some $Q' : rDA_LL$, we must define $eta_Q' : Q' -> R(I(Q'))$.
  We can define this as the _identity_ morphism, since this round trip is a no-op both ways.

  For the counit, for some $Q : DA_LL$, we must define $eps_Q : I(R(Q)) -> Q$.
  Since $R(Q)$ contains the subset of $Q$'s states that are reachable, it's actually a subset.
  So $eps_Q$ can just be a subset inclusion (notice that unlike above, $I(R(Q))$ may be a different object than just $Q$).
  
  Let's check that our definitions for unit and counit satisfy the triangle identities:

  #align(center, table(
    columns: (auto, auto),
    stroke: none,
    column-gutter: 3em,
    
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJJIl0sWzEsMCwiSSBSIEkiXSxbMSwxLCJJIl0sWzAsMSwiSSBldGEiLDAseyJsZXZlbCI6Mn1dLFsxLDIsImVwc2lsb24uYWx0IEkiLDAseyJsZXZlbCI6Mn1dLFswLDIsIjFfSSIsMix7ImxldmVsIjoyfV1d
    align(center, diagram({
    	node((0, 0), [$I$])
    	node((1, 0), [$I R I$])
    	node((1, 1), [$I$])
    	edge((0, 0), (1, 0), [$I eta$], label-side: left, "=>")
    	edge((1, 0), (1, 1), [$epsilon.alt I$], label-side: left, "=>")
    	edge((0, 0), (1, 1), [$1_I$], label-side: right, "=>")
    })),
  
    // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJSIl0sWzEsMCwiUiBJIFIiXSxbMSwxLCJSIl0sWzAsMSwiUiBldGEiLDAseyJsZXZlbCI6Mn1dLFsxLDIsImVwc2lsb24uYWx0IFIiLDAseyJsZXZlbCI6Mn1dLFswLDIsIjFfUiIsMix7ImxldmVsIjoyfV1d
    align(center, diagram({
    	node((0, -1), [$R$])
    	node((1, -1), [$R I R$])
    	node((1, 0), [$R$])
    	edge((0, -1), (1, -1), [$R eta$], label-side: left, "=>")
    	edge((1, -1), (1, 0), [$epsilon.alt R$], label-side: left, "=>")
    	edge((0, -1), (1, 0), [$1_R$], label-side: right, "=>")
    }))
  ))

  For the first triangle, we can write this equationally as:

  $ eps I compose I eta = 1_I $

  Instantiating this with our $Q' : rDA_LL$:

  $ (eps I)_Q' compose (I eta)_Q' &= (1_I)_Q' \
  I(Q') -->^((I eta)_Q') I(R(I(Q'))) -->^((eps I)_Q') I(Q') &= I(Q') -->^((1_I)_Q') I(Q')
  $

  Well, we have defined $eta$ to be a no-op, so the left side $(I eta)_Q'$ is the identity.
  Since $eps$ is a subset inclusion, for reachable automata, $(eps I)_Q'$ is _also_ the identity.
  Thus, identity compose identity is the identity.

  For the second triangle, we can write this equationally as:

  $ eps R compose R eta = 1_R $

  Instantiating this with $Q : DA_LL$:
  
  $
  (eps R)_Q compose (R eta)_Q = (1_R)_Q \
  R(Q) -->^((R eta)_Q) R(I(R(Q))) -->^((eps R)_Q) R(Q) = R(Q) -->^((1_R)_Q) R(Q)
  $

  Again, we have $eta$ is a no-op, so the left side is the identity.
  The right side goes from reachable to reachable, so the subset inclusion $eps$ is simply restricted to the identity by default here.

  Both triangle inequalities check out, so our adjunction is defined.

  
  // In other words, we are looking for a $Q' : rDA_LL$ such that there are morphisms $f : I(Q') -> Q$ and $g : Q' -> R(Q)$ that obeys the following commutative diagram in $DA_LL$:

  // #align(center, diagram($
  //   I(Q') edge("d", "->", I(g))
  //   edge("dr", "->", f) \
  //   I(R(Q)) edge("->", epsilon.alt_Q, label-side: #right) & Q
  // $))

  // or equationally:

  // $ epsilon.alt_Q compose I(g) = f $

  // where $epsilon.alt : I compose R => id_DA_LL$ is the counit of the adjunction.

  // Let's sketch out what $R$ should look like.
  // Essentially, to go from $DA_LL$ to $rDA_LL$, we want to find the closest approximation of $Q$ inside $rDA_LL$.
  // Well, if there are unreachable states inside our automaton, we would like to discard those states.
  // To reuse machinery we have already constructed, we can define $R$'s action on objects $Q$ by taking the codomain of the morphism $Init -> Q$.
  // By definition, then, $R(Q)$ is reachable.

  // Next, we should define the elements of the adjunction, starting with $epsilon.alt_Q : I(R(Q)) -> Q$, the counit.
  // Since $I(R(Q))$ is a subset of the states in $Q$, this morphism is actually a subset inclusion.
  // Then, 
]

Similarly, for $oDA_LL$:

#theorem[$oDA_LL$ is a reflective subcategory of $DA_LL$. In other words, supposing $I : oDA_LL arrow.r.hook DA_LL$ is the inclusion functor, there exists a functor $Omicron : DA_LL -> oDA_LL$ such that $ O tack.l I $] <oDALReflectiveSubcategory>

#exercise[Prove @oDALReflectiveSubcategory. The proof should look mostly like a dualization of the proof of @rDALCoreflectiveSubcategory.]

The corresponding adjoint functor for $rDA_LL$, called $R$, then restricts automata in the input category to their reachable subset.
Similarly, the corresponding adjoint functor for $oDA_LL$, called $O$, restricts automata in _its_ input category to their observable subset.
And then at the bottom, $mDA_LL$ is both a reflective subcategory and co-reflective subcategory of $oDA_LL$ and $rDA_LL$, respectively.
Let us update the diamond diagram to see these new functors:

#align(center, diagram(spacing: (1.5cm, 2cm), {
  let shift = 2pt
  let obend = 30deg
  let ibend = 15deg
  let tbend = 10deg
// & DA_LL
node((0, -1), name: <DAL>, $DA_LL$)
node((-1, 0), name: <rDAL>, $rDA_LL$)
node((1, 0), name: <oDAL>, $oDA_LL$)
node((0, 1), name: <mDAL>, $mDA_LL$)

edge(<rDAL>, <DAL>, "hook->", shift: shift, bend: obend)
edge(<rDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<DAL>, <rDAL>, "->", shift: shift, bend: ibend, $R$)

edge(<oDAL>, <DAL>, "hook->", shift: -shift, bend: -obend)
edge(<oDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<DAL>, <oDAL>, "->", shift: -shift, bend: -ibend, $O$)

edge(<mDAL>, <rDAL>, "hook->", shift: -shift, bend: -ibend)
edge(<rDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<rDAL>, <mDAL>, "->", shift: -shift, bend: -obend, $O$)

edge(<mDAL>, <oDAL>, "hook->", shift: shift, bend: ibend)
edge(<oDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<oDAL>, <mDAL>, "->", shift: shift, bend: obend, $R$)
}))

Finally, due to our self-dual functor $F2$, we have a functor between $rDA_LL$ and $oDA_LL$, that reflects reachable automata into observable automata in the _reverse_ language:
Thus, our final minimization morphism is simply a concatenation of a series of functors:


#align(center, diagram(spacing: (1cm, 1.5cm),
  edge-stroke: gray,
  {
    
  let shift = 2pt
  let obend = 30deg
  let ibend = 15deg
  let tbend = 10deg
  
node((-2, -1), name: <DAL>, rect($DA_LL$))
node((-3, 0), name: <rDAL>, $rDA_LL$)
node((-1, 0), name: <oDAL>, $oDA_LL$)
node((-2, 1), name: <mDAL>, rect($mDA_LL$))

edge(<rDAL>, <DAL>, "hook->", shift: shift, bend: obend)
edge(<rDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<DAL>, <rDAL>, "->", shift: shift, bend: ibend, text(fill: red, $R$), stroke: 2pt + red)

edge(<oDAL>, <DAL>, "hook->", shift: -shift, bend: -obend)
edge(<oDAL>, <DAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<DAL>, <oDAL>, "->", shift: -shift, bend: -ibend, $O$)

edge(<mDAL>, <rDAL>, "hook->", shift: -shift, bend: -ibend)
edge(<rDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<rDAL>, <mDAL>, "->", shift: -shift, bend: -obend, $O$)

edge(<mDAL>, <oDAL>, "hook->", shift: shift, bend: ibend)
edge(<oDAL>, <mDAL>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<oDAL>, <mDAL>, "->", shift: shift, bend: obend, $R$)


node((2, -1), name: <DAL2>, $opp(DA_rev(LL))$)
node((1, 0), name: <rDAL2>, $opp(rDA_rev(LL))$)
node((3, 0), name: <oDAL2>, $opp(oDA_rev(LL))$)
node((2, 1), name: <mDAL2>, $opp(mDA_rev(LL))$)

edge(<rDAL2>, <DAL2>, "hook->", shift: shift, bend: obend)
edge(<rDAL2>, <DAL2>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<DAL2>, <rDAL2>, "->", shift: shift, bend: ibend, $opp(R)$)

edge(<oDAL2>, <DAL2>, "hook->", shift: -shift, bend: -obend)
edge(<oDAL2>, <DAL2>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<DAL2>, <oDAL2>, "->", shift: -shift, bend: -ibend, $opp(O)$)

edge(<mDAL2>, <rDAL2>, "hook->", shift: -shift, bend: -ibend)
edge(<rDAL2>, <mDAL2>, stroke: 0pt, label-side: center, label-angle: -45deg, $tack.b$, bend: -tbend)
edge(<rDAL2>, <mDAL2>, "->", shift: -shift, bend: -obend, $opp(O)$)

edge(<mDAL2>, <oDAL2>, "hook->", shift: shift, bend: ibend)
edge(<oDAL2>, <mDAL2>, stroke: 0pt, label-side: center, label-angle: 45deg, $tack.t$, bend: tbend)
edge(<oDAL2>, <mDAL2>, "->", shift: shift, bend: obend, text(fill: red, $opp(R)$), stroke: 2pt + red)

edge(<rDAL>, <oDAL2>, "->", stroke: 2pt + red, bend: 5deg, text(fill: red, $F2$))
edge(<mDAL2>, <mDAL>, "->", stroke: 2pt + red, bend: 5deg, text(fill: red, $opp(F2)$))
}))

#theorem(title: [Brzozowski minimization algorithm])[
  The functor:
  $ (opp(F2) compose opp(R) compose F2 compose R) : DA_LL -> mDA_LL $
  minimizes deterministic automata.
]

#proof[
Due to the way the functors were constructed, we get the following two properties "for free" (ignoring all the work that went into constructing the functors):
- the series of functors preserves the language being recognized (notice the subscript $LL$)
- the resulting automaton is minimal (by definition of $mDA_LL$)

Thus, the theorem holds by construction.
]

// == Logic

// @cirstea_modal_2011 @kurz_coalgebras_nodate

// A formal logic includes some atomic propositions, some connectives ($and$, $or$, $not$), and some rules that dictate how we can inductively build formulas using connectives to assign truth values to the resulting formulas.

// We'll introduce a basic logic first, then look at modal logic.
// Then, we will see how coalgebras can be used to abstract away logics, and motivate some of the design.
// Let's begin with a basic propositional logic:

// #definition(title: [Syntax of propositional logic])[
//   A formula $phi$ is composed of:
// $ phi ::= p | top | bot | not phi | phi and phi | phi or phi | phi -> phi $
//   where $p in Prop$, the set of atomic propositions.
// ]

// A formula can be evaluated under a context $Gamma$ which holds the truth value of each proposition.
// The result of the evaluation will be a truth value under the proposition.
// We will write $Gamma |= phi$ if $phi$ evaluates to $top$, given the values of the atomic propositions in $Gamma$.

// Modal logic is a logic that contains modalities, the most well-known of which is the "necessity" modality.
// This gives us a way to express something that is true in other possible worlds, as opposed to only being true at the current world.
// Each world may have different values for variables, leading to different outputs for the same formula.
// When a proposition $phi$ is necessarily true in all worlds that can be reached from the current world, this is written $square phi$.

// There are a ton of concepts that can be studied as modalities, such as eventuality, knowledge/belief, obligation/permission, etc.
// Even staged compilation can be represented as a modality.
// These different modalities will have different notions of what other worlds are reachable.
// For example, in temporal logic, reachability is realized as being able to evolve from one world state to another over time, whereas in knowledge, reachability has to do with the passing of messages.
// This makes modal logic a great addition to a type theory.

// Here, we'll start with introducing a basic modal type theory, $KK$, and then analyzing it through the lens of coalgebras.


// #definition(title: [Syntax of $KK$])[
//   We define the modal language as:

// $ phi ::= p | top | bot | not phi | phi and phi | phi or phi | phi -> phi | square phi $

// where
// - $p in Prop$, a set of atomic propositions
// - $square phi$ is the box modality, representing necessity in this case
// ]

// We discussed previously that the meaning of the $square phi$ notation will depend on truth in relation to other worlds.
// A world is simply another context with different values for each of the atomic propositions made available to the language.
// Worlds are related to each other by an accessibility relation $R$, which is left as a parameter to the language.
// We write $w R v$ to mean world $v$ is reachable from world $w$ via the relation.
// There are no stipulations on $R$ whatsoever, although some extensions of $KK$ may require that $R$ be reflexive, symmetric, or transitive.

// Under this system, for $square phi$ ("it is necessary that $phi$") to hold true at world $w$, it must be true that $phi$ holds true at all worlds $v$ reachable from $w$.

// #definition(title: [Kripke model])[
//   A *Kripke model* is a 3-tuple $(X, R, V)$ where:
//   - $X$ is the set of all worlds
//   - $R$ is the accessibility relation over $X$, that is: $R subset X times X$
//   - $V : X -> PP(Prop)$ is a valuation, which maps any world to the set of atomic propositions that hold true in that world
// ]

// Often, we only really care about the formulas that hold under any possible set of atomic propositions, so we drop the $V$:

// #definition(title: [Kripke frame])[
//   A *Kripke frame* is a tuple $(X, R)$ where:
//   - $X$ is the set of all worlds
//   - $R$ is the accessibility relation over $X$, that is: $R subset X times X$
// ]

// Now that we have all the syntax set up, we must talk about the semantics.
// The rules of modal logic primarily follow from first-order logic, with the exception of the box modality rule, which we will discuss a bit further in detail.

// #definition(title: [Semantics for $K$])[
//   For any $(X, R, V, x)$ such that $(X, R, V)$ is a Kripke model and $x in X$:
  
//   - $(X, R, V, x) |= p$, if $p in V(x)$
//   - $(X, R, V, x) cancel(|=) bot$
//   - $(X, R, V, x) |= phi -> psi$, if $(X, R, V, x) |= phi$ implies $(X, R, V, x) |= psi$
//   - $(X, R, V, x) |= square phi$, if for any $y in X$, it holds that $x R y$ implies $(X, R, V, y) |= phi$

//   Additionally, a proposition $phi$ that holds under any frame is written $|= phi$.
// ]

// The $square phi$ rule makes formal the vague notion of truth #TODO

// What kinds of properties can we prove about this structure?
// Let's start with a simple one:

// #lemma[For any Kripke frame $(X, R)$ where $R$ is a reflexive relation (that is, $x R x$ for all $x in X$), it is true that $square p -> p$.]

// #proof[
//   Let $x in X$, and $V$ be the valuation.
//   We want to show that if $(X, R, V, x) tack.double square p$, then $(X, R, V, x) tack.double p$.
//   Due to $(X, R, V, x) tack.double square p$, we know that for any $y$ such that $x R y$, it is true that $(X, R, V, y) tack.double p$.
//   Using the fact that $x R x$, we can instantiate $y$ with $x$ and derive that $(X, R, V, x) tack.double p$.
// ]

// -------------------------------------------------------------

// There is another modal operator, $diamond$, which represents possibility.
// So $diamond phi$ can be read "it is possible that $phi$".
// This operator is often left out of the core calculus simply for the fact that it can be defined in terms of $square$:

// $ diamond phi :equiv not square not phi $

// In plain E  nglish, "it is not necessary that $phi$ doesn't hold true" is logically equivalent to saying "it is possible that $phi$ holds true".

// #TODO we must first identify a signature functor by which 
// Interestingly, due to this multiple-worlds setup, it is possible to think of our modal logic as a coalgebra for the signature functor:

// $ F(X) = PP(X) $

// where $PP(X)$ is the powerset of $X$.
// Under this interpretation, our structure map $xi : X -> PP(X)$ can be understood as mapping a world to the possible next worlds.
// Let's explore how th rest of modal logic can be translated into coalgebraic language.

= Exercises

Here is a table of some of the exercises that have been distributed throughout the explainer.

#outline(title: none, target: figure.where(kind: "exercise"))

#bibliography("zotero.bib", style: "chicago-author-date")