---
title: Foundations
---

# What are the foundations of this project?

Foundations of mathematics are almost entirely irrelevant to mathematicians. 
This is still mostly true when using a proof assistant.
But of course they are very relevant to the question this page is meant
to answer.
Another reason to discuss foundations is they have a huge impact on how
the proof assistant can fill in the implicit details of our mathematical
statements.
Specific examples will use the Lean theorem prover,
that we used for the perfectoid spaces project.
But almost everything on this page applies verbatim to Coq.
Indeed, the calculus of inductive constructions (the foundational system
we will briefly describe) was invented for Coq.
Section 3.1 of the
[Mathematical Components Book](https://math-comp.github.io/mcb/),
and the first four chapters of 
[Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/)
are much longer (and much more authoritative) explanations about the
same topic.

## Types and typing judgments

Most mathematicians that get cornered into saying something about
foundations mention Zermelo-Fraenkel set theory
(with or without knowing anything about that topic).
This is not the kind of foundations Lean uses,
it uses type theory.
The main issue with set theory as a foundational framework is that it is
completely unstructured. 
Everything is a set, 
and there are only two relations: equality and membership. 
For instance $\pi \in \cos$ is a well-formed mathematical statement
(which is hopefully wrong). 
The huge variety of nature of mathematical objects is, 
from this foundational perspective, 
only a psychological layer that we put on top of set membership. 
By contrast, as indicated by its name, 
type theory very carefully keeps track of the type of mathematical objects. 
Just like every mathematicial object is a set when formalized using set theory, 
it is a *term* having some *type* when formalized in type theory.
Type theory provides many[^1] powerful ways of combining existing types of
objects into new ones. 
The most fundamental such combination takes two types $A$ and $B$ and
returns the type $A \to B$ of functions from $A$ to $B$
(at this point "function" is only a name). 
Complicated terms are made from juxtaposition of simpler ones, 
and the typing rules dictate the type of any (legal) juxtaposition. 
For instance, if $x$ is a term with type $A$ and $f$ is a term with type
$A \to B$ then $f x$,
also written as $f(x)$, has type $B$. 
It is crucial to understand that this so-called "typing judgment" happens at the meta-theoretic level,
not inside the formalized theory. 
It does not need to be proven inside the theory, 
just as we don't need to prove the rules of logic when doing regular
mathematics.
Since typing information is so important, there is a notation for it.
We write $x : A$ to say that $x$ has type $A$.

In order to easily express all of mathematics, 
it is important that types are allowed to depend on terms.
For instance, given a term $n$ with type $\NN$, 
we can form the type $\RR^n$.
Such a type is called a dependent type.

Up to this point, type theory is actualy closer to regular maths than
set theory. What is much more exotic is how the reduction rules coming
from $\lambda$-calculus enter the game. There is a conversion relation
on terms. For instance, if we consider the term 
$(n \mapsto 2\cdot n) : \NN \to \NN$,
then the term $(n \mapsto 2\cdot n) 3$ converts to
$2\cdot 3$ which, by definition of multiplication, converts to $6$.
Again this happens at the meta-theoretic level, 
it cannot be proved or disproved inside the theory, only observed.  
Together with the typing rule given above, 
this conversion rule justifies the name "function type". 
We will say that $(n \mapsto 2 \cdot n) 3$ is
*definitionally* equal to $6$. 
In this page, this word will always be used in this very specific
technical sense.

Unfortunately, computer scientists have strong emotional bounds to a
very weird way of denoting functions like $n \mapsto 2\cdot n$.
They write it as $\lambda\\, n, 2\cdot n$ or,
when they need to make the variable type explicit,
$\lambda\\, n : \NN, 2\cdot n$.
Getting used to that is surprisingly not so hard.

## Curry-Howard and proofs

Applying typing rules is the core activity of a proof assistant based on
type theory (such as Lean), and it is done by the so-called *kernel*. 
Remarkably, this includes checking proofs, thanks to the Curry-Howard
isomorphism,
as we will now explain.
Each mathematical statement is also a type of mathematical object, 
and a proof of such a statement is a term having this type.
Proof checking is thus a particular kind of typing judgment.
For instance, if $P$ and $Q$ are statements, 
then the statement $P \implies Q$ is the function type $P \to Q$.
Indeed there is no need to introduce a new typing judgment since we want
exactly the same rule as above:
given $h_P : P$ (i.e. $h_P$ is a term of type $P$, i.e. $h_P$ a proof of $P$) 
and $h : P \to Q$ (i.e. $h$ is a proof that $P$ implies $Q$) then
$h\\, h_P : Q$ (ie. $h\\, h_P$ is a proof of $Q$).

Type themselves live in so-called universes. 
Universes forms a countable sequence.
This is necessary in order to avoid paradoxes analogous
to Russell's barber paradox in set theory,
but this kind of consideration is not relevant to us.
More importantly, this allows to see types as terms.
Mathematical statements are types whose universe is called $\Prop$.
Usual mathematical types, like $\NN$ or $\RR$ have universe $\Type$.
Using this and dependent types, we can now express the idea of a
predicates, 
i.e. mathematical statement depending on a mathematical object.
For instance, being even is a predicate depending on a natural number,
hence it has type $\NN \to \Prop$.
For any given natural number $n$, we get the type $\mathrm{even}(n) : \Prop$, 
and a term of type $\mathrm{even}(n)$ is a proof that $n$ is even.

In order to express the universal quantifier,
one needs a mild generalization of function types, 
where the target type can depend on the input value.
There are sometimes called dependent function types.
For instance, a proof of the statement $\forall n, \mathrm{even(2n)}$ is
seen as the function sending a natural number $n$ to a proof that $2n$
is even.
Say we have a proof of this statement, ie a term
$\mathrm{double\\_even} : \forall n, \mathrm{even(2n)}$,
and a term 
$\mathrm{succ\\_odd} : \forall n, \mathrm{even}(n) \to \mathrm{odd(n+1)}$.
We now want to use those to prove that, for every $n$, 
$2n+1$ is odd.
It means we need a term whose type is
$\forall n, \mathrm{odd(2n+1)}$,
ie a function with input $n$ and output a proof that
$2n+1$ is odd.
Given any $n$, it suffices to apply $\mathrm{succ\\_odd}$ to 
$2n$ and a proof that $2n$ is even.
And $\mathrm{double\\_even}\\, n$ is precisely the latter.
So our full proof term is 
$n \mapsto \mathrm{succ\\_odd}\\; 2n\\; (\mathrm{double\\_even}\\, n)$.
This is almost valid Lean code, we only need to remember
to use $\lambda$ instead of $\mapsto$,
and also remember computers don't like implicit multiplication.
```lean
lemma test : ∀ n, odd (2*n + 1) :=
λ n, odd_succ (2*n) (double_even n)
```

Now, you may wonder how Lean know that $n$ has type $\NN$ in the above
snippet.
This is already using the benefits of carefully tracking the types of
mathematical objects.
Indeed, we assumed above that $\mathrm{even}$ and $\mathrm{odd}$ have
type $\NN \to \Prop$,
so Lean can infer that, in the statement,
`2*n + 1` necessarily has type $\NN$,
and then so does `n`.
The same reasonning allows us to start the proof term with `λ n` instead
of `λ n : ℕ`.
This so-called unification procedure is actually much more powerful.
For instance, one can leave holes using `_` wherever a term is 
expected, and Lean will try to fill this hole by unification.
In our example, we could have written:
```lean
lemma test : ∀ n, odd (2*n + 1) :=
λ n, odd_succ _ (double_even _)
```
The first hole is filled by unifying the expected type
`odd (2*n + 1)` with the type of `odd_succ _` which is
`even ?₁ → odd (?₁+1)` for some unknown `?₁`. 
This first unification succeeds by setting `?₁ = 2*n`.
Then Lean needs to unify the type `even (2*?₂)` of `double_even _` with 
the expected `even (2*n)` and again there is only one solution, which is `?₂ = n`.
Of course we don't gain much in the simple example, but unification is
crucial in more complicated examples.

One should note that the unification process is not part of the kernel.
The kernel (which needs to be trusted, hence very simple) receives 
the fully elaborated term `λ n : ℕ, odd_succ (2*n) (double_even n)`,
applies typing rules to compute its type, 
and compares with the fully elaborated statement
`∀ n : ℕ, odd (2*n + 1)`.
This process is so much simpler than being a full proof assistant
that there are at least three alternative checkers,
written in three different programming languages
(Lean itself is written in C++, and there are checkers written
in Haskell, Scala, and Rust).

Even with good elaboration, 
writing proof terms by hand very quickly becomes unsustainable.
There is a huge layer called the tactic framework whose role is
to interact with the user,
and write proof terms off stage. For example, it takes a very
long time to prove from first principles
that $(a+b)^3=a^3+3*a*b^2+3*a*b^2+b^3$ for integers $a$ and $b$,
the main problem being that re-arranging the sum of eight terms
using only commutativity and associativity is incredibly tedious
for a human.
However Lean's `ring` tactic produces a proof of this immediately
without the user having to worry about doing it by hand.
Again this tactic layer is not trusted, it builds terms whose type
is checked by the kernel.
To put it another way,
tactics create candidates for proofs,
and then the kernel checks that they are actually correct proofs.

## Inductive types

We haven't yet described enough ways to build types.
For instance, we haven't seen have to build the type $\NN$.
Surprisingly related, we have explained universal quantifiers,
but not existential ones, conjunctions and disjunctions.
All those things are inductive types.

The following is Lean's definition of natural number, following Peano's
axioms:
```lean
inductive ℕ
| zero : ℕ
| succ : ℕ → ℕ
```
It reads: there are exactly two ways to build a term of type `ℕ`, either
the constant `zero`, or apply the function `succ` to a term with type
`ℕ`.
Implicitly, it also says that those two ways are unrelated
(in particular it guarantees that `zero` is not equal to `succ n` for
any `n`).

Remember that, deep down, the only things that exist are terms and types, 
and, at the meta-theoretic level, typing judgments and term conversions
(aka definitional equality). 

The definition does a number of those deep things. 
Visibly, it postulates the existence of two terms `zero : ℕ` and 
`succ : ℕ → ℕ`.
But it also postulate the existence of the corresponding induction
principle.
This is a term whose type is a bit complicated,
but the important thing is it allows to recover the usual proof by
induction principle (if, for some predicate $P$ on $\NN$,
$P\\, 0$ holds and $P\\\, d \implies P\\, (succ\\, d)$ then $P\\, n$ hold for
all $n$) and the possibility of defining sequences by induction (given 
$u_0$ and the constraint $u_{n+1} = f(u_n)$).

Again this is much closer to mathematical intuition than building a
model of Peano's axioms in ZF set theory.

More generally, inductive types can take parameters (there is none in our example),
have arbitrarily many "constructors" (here there are two: `zero` and `succ`) which can
take arbitrarily many arguments (no argument in the case of `zero`
and one argument in the case of `succ`).
These arguments can be terms of the type being defined (as in `succ`),
modulo some technical condition which prevents circular constructions.

Amazingly, together with dependent function types, 
inductive types allow to build everything else.
For instance, amongst logical operations, we have described only
implication and the $\forall$ quantifier.
Everything else is defined using inductive types.
For instance, the definition of the logical operation "and" is:
```lean
inductive And (P Q : Prop) :
| intro (h : P) (h' : Q) : And
```
It says that, for any two statements `P` and `Q`,
one can define an inductive type `And P Q`,
and the only way to build a term having this type
is to use the function `intro` which takes a proof
`h` of `P` and a proof `h'` of `Q`.
The corresponding induction principle guarantees
that we can do something using a term whose type is `And P Q`
if we can do it with the ingredients taken by `intro`.

As an exercise, you can think about the definition of the "or" operator:
```lean
inductive Or (P Q : Prop) :
| left (h : P) : Or
| right (h' : Q) : Or
```

Note that this time we have two constructors, and hence two ways of
constructing a term of type `Or P Q`.

Surprisingly, even equality is not a primitive notion in these
foundations, and is defined as an inductive type.
Now we can finally point out the deepest difference between
foundations based on set theory and type theory. In order to use set
theory, one needs to have developped (first order) logic, with its
logical connective and deduction rules. And then proofs have nothing in
common with mathematical objects, they live purely at the meta-theoretic
level. In dependent type theory with inductive types, logic is expressed
inside the theory, and proofs are mathematical objects living inside the
theory.

Inductive types also allow us to define structures.
For instance, a commutative magma structure on a type $M$
is made of a multiplication operation and the assertion that
this multiplication is commutative. 
Multiplication `mul` takes two terms with type $M$ and returns a term with
type $M$.
```lean
inductive comm_magma (M : Type)
| make (mul : M × M → M) (comm : ∀ a b : M, mul (a, b) = mul (b, a)) : comm_magma
```
Here the constructor is called `make`, it says to build a term
whose type is `comm_magma M` we need exactly a function `mul : M × M → M`
and a term `comm` proving that this operation is commutative.
The induction principle says that anything which follows from those
ingredients follows from having fixed a commutative monoid structure on
`M`. 
Of course Lean provides many facilities in order to define and use such
structures,
including facilities for building rich structures extending simpler
ones,
but this does not change anything about these foundations.

##  The axiom of choice and computation

One often reads that proof assistant users love constructive mathematics and
don't like the axiom of choice.
A much better approximation of the truth is that some users of proof
assistants have those tastes.
Proof assistants that we know have no issue at all postulating the axiom
of choice, and Lean users in general don't even notice when they use it
(although Lean does report it if asked about it). Using the axiom
of choice in some code might make the corresponding functions noncomputable.
However many mathematicians are often far more concerned with reasoning about
functions (that is, proving theorems about them) than actually computing
them, and so noncomputability is not an issue in practice.
