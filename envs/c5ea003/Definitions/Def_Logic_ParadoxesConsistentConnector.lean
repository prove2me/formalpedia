-- Prove2me | Definitions.Def_Logic_ParadoxesConsistentConnector
-- name    : Logic_ParadoxesConsistentConnector
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:59:53.634047+00:00
-- url     : https://prove2.me/theorems/b491cd51-e8b9-4cb7-8dd9-4527ba31abdb
-- title:
--   Aether Catalog definitions — Logic_ParadoxesConsistentConnector
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ParadoxesConsistentConnector`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ParadoxesConsistentConnector.lean by skeleton subtraction
import Mathlib

/-!
# Paradoxes as Theorems: a Bridge between Boolean Algebra and Self-Reference

This self-contained file makes precise the slogan *"the Liar, Berry and Russell
paradoxes can all be **theorems** of a consistent formal system, but only if
classical (Boolean) logic is rejected."*

The mathematical content is a **cross-domain bridge**:

* On the *algebraic* side we work inside an arbitrary `BooleanAlgebra`, a purely
  order-theoretic / lattice object.
* On the *logical* side we study *self-negating* sentences — the abstract shape
  shared by the Liar (`this sentence is false`), Russell (`the set of all sets
  that do not contain themselves`) and Berry (`the least number not nameable in
  fewer than nineteen syllables`).  In every one of these, a sentence is
  equivalent to *its own negation*.

The connecting theorem `boolean_neg_fixpoint_trivial` says:

> In **any** Boolean algebra, a truth value equal to its own complement forces
> the algebra to collapse (`⊥ = ⊤`).

Contrapositively, a *nontrivial* Boolean algebra admits **no** negation
fixed point, so a consistent theory containing a self-negating (Liar-style)
sentence cannot be Boolean-valued.  Hence *paradoxes as theorems require
rejecting classical logic.*

We then exhibit the positive half: **Belnap's four-valued logic** `BV`
(`T`rue, `F`alse, `B`oth, `N`either) *does* have a designated negation
fixed point `B`, and we build an explicit six-sentence paraconsistent theory
in which three distinct paradox sentences (Liar / Russell / Berry) are all
provable *gluts* while the theory stays nontrivial and non-explosive.

Nothing here depends on any other project file; it imports only Mathlib.
-/

namespace ParadoxesConsistentConnector

/-! ## 1. The classical (Boolean) obstruction

The bridge theorem: any negation fixed point in a Boolean algebra trivialises it.
This is the algebraic core of *"the Liar is inconsistent classically."* -/





/-! ## 2. Belnap's four-valued algebra `BV`

To make paradoxes into theorems we move to a paraconsistent, four-valued setting.
`B` ("both true and false", a *glut*) and `N` ("neither", a *gap*) are the two
non-classical values. -/

/-- The four Belnap truth values. -/
inductive BV | T | F | B | N
deriving DecidableEq, Repr, Fintype

namespace BV

/-- Belnap negation: swaps `T`/`F` and fixes the non-classical values `B`, `N`. -/
def neg : BV → BV
  | T => F | F => T | B => B | N => N

/-- Designation: a value counts as *asserted / provable* iff it is at-least-true. -/
def des : BV → Bool
  | T => true | B => true | F => false | N => false

/-- Belnap conjunction (meet in the truth order `F ≤ N,B ≤ T`). -/
def conj : BV → BV → BV
  | T, x => x | x, T => x
  | F, _ => F | _, F => F
  | B, B => B | N, N => N
  | B, N => F | N, B => F

/-- Belnap disjunction (join in the truth order). -/
def disj : BV → BV → BV
  | F, x => x | x, F => x
  | T, _ => T | _, T => T
  | B, B => B | N, N => N
  | B, N => T | N, B => T






end BV

/-! ## 3. An explicit consistent paraconsistent theory

We package a "formal system" as a valuation of sentences into `BV` together with
a syntactic negation that is *coherent* with Belnap negation.  Provability means
the sentence is designated. -/

open BV

/-- A paraconsistent theory over a sentence type `S`: a truth-value assignment,
a syntactic negation, and a coherence condition tying them together. -/
structure ParaTheory (S : Type) where
  /-- Truth value of each sentence. -/
  val : S → BV
  /-- Syntactic negation of each sentence. -/
  sneg : S → S
  /-- Syntactic negation realizes Belnap negation on truth values. -/
  coherent : ∀ s, val (sneg s) = neg (val s)

/-- A sentence is *provable* iff its truth value is designated. -/
def ParaTheory.prov {S} (M : ParaTheory S) (s : S) : Prop := des (M.val s) = true

/-- A sentence is a *glut* (a genuine paradox) iff both it and its negation are
provable. -/
def ParaTheory.glut {S} (M : ParaTheory S) (s : S) : Prop :=
  M.prov s ∧ M.prov (M.sneg s)

instance {S} (M : ParaTheory S) (s : S) : Decidable (M.prov s) := by
  unfold ParaTheory.prov; infer_instance


/-! ### The six-sentence witness model

Sentences `0,1,2` are the three paradox witnesses (Liar / Russell / Berry),
each a self-negation fixed point valued `B`.  Sentence `3` is a genuine truth,
`4` a genuine falsehood (the non-explosion witness), `5` a gap. -/

/-- Truth-value assignment: three gluts, one truth, one falsehood, one gap. -/
def paradoxVal : Fin 6 → BV := ![B, B, B, T, F, N]

/-- Syntactic negation: the three paradox sentences are fixed points; `3`/`4`
swap; the gap `5` is fixed. -/
def paradoxNeg : Fin 6 → Fin 6 := ![0, 1, 2, 4, 3, 5]

/-- The explicit six-sentence paraconsistent theory. -/
def paradoxModel : ParaTheory (Fin 6) where
  val := paradoxVal
  sneg := paradoxNeg
  coherent := by decide




/-! ## 4. The dichotomy, stated in one place

Putting the two sides of the bridge together. -/


end ParadoxesConsistentConnector


