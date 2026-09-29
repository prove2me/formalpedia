-- Prove2me | Definitions.Def_Novelty_InfinitesimalFiniteProbability
-- name    : Novelty_InfinitesimalFiniteProbability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:29:29.71721+00:00
-- url     : https://prove2.me/theorems/c93e2842-ea8c-4a06-95ae-ba5e941fb5e3
-- title:
--   Aether Catalog definitions — Novelty_InfinitesimalFiniteProbability
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.InfinitesimalFiniteProbability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/InfinitesimalFiniteProbability.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024 Harmonic Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A finite infinitesimal probability model

This file builds, for each `n : ℕ`, a concrete finitely additive probability measure whose
values live in an ordered ring of *infinitesimals* rather than in `ℝ`.  The value type is the
ring of pairs `LexRat = ℚ × ℚ`, where a pair `(a, b)` is interpreted as the formal expression
`a + b·ε` with `ε` a positive infinitesimal.  Addition, subtraction and negation are the usual
componentwise operations on pairs, but the order is **lexicographic**: `(a₁, b₁) ≤ (a₂, b₂)` iff
`a₁ < a₂`, or `a₁ = a₂` and `b₁ ≤ b₂`.  Under this order `ε = (0, 1)` is positive but smaller than
every positive rational `(q, 0)`, i.e. it is a genuine infinitesimal.

## The model

The sample space for parameter `n` is `Option (Fin n)`.  The `n` "visible" atoms `some i` each
carry the infinitesimal weight `ε`, while the single "reservoir" atom `none` carries weight
`1 - n·ε`.  The reservoir weight is chosen exactly so that the total mass is

  `n · ε + (1 - n·ε) = 1`,

making the measure normalized.  Because the reservoir absorbs the deficit `-n·ε` in its
infinitesimal component while keeping a real component equal to `1`, it remains lexicographically
positive; meanwhile each visible atom has probability `ε`, which is positive yet infinitesimally
small — strictly below `1` and below every positive standard probability.

## Main results

* `LexRat.eps_infinitesimal` : `ε` is below every positive rational.
* `prob_eq_closed_form` : a closed form for the probability of an arbitrary event.
* `prob_nonneg` : every event has lexicographically nonnegative probability.
* `prob_union_disjoint` : finite additivity.
* `prob_univ` : the total mass is `1`.
* `visible_singleton_infinitesimal` : each visible atom has infinitesimal probability `ε < 1`.
-/

/-- The value type of the infinitesimal probability model: a pair `(a, b)` read as `a + b·ε`. -/
abbrev LexRat := ℚ × ℚ

namespace LexRat

/-- Lexicographic `≤` on `LexRat`. -/
def lexLe (x y : LexRat) : Prop := x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 ≤ y.2

/-- Lexicographic `<` on `LexRat`. -/
def lexLt (x y : LexRat) : Prop := x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2

/-- Lexicographic nonnegativity: `(0,0) ≤ x`. -/
def Nonneg (x : LexRat) : Prop := lexLe (0, 0) x

/-- The unit `1 = (1, 0)`. -/
def one : LexRat := ((1 : ℚ), (0 : ℚ))

/-- The infinitesimal `ε = (0, 1)`. -/
def eps : LexRat := ((0 : ℚ), (1 : ℚ))

/-- Embedding of a rational `q` as the standard value `(q, 0)`. -/
def ofRat (q : ℚ) : LexRat := (q, 0)





end LexRat

namespace InfinitesimalProbability

open LexRat

/-- The atom weights for parameter `n`: the reservoir atom `none` carries `1 - n·ε`, while each
visible atom `some i` carries `ε`. -/
def atomWeight (n : ℕ) : Option (Fin n) → LexRat
  | none => ((1 : ℚ), -(n : ℚ))
  | some _ => ((0 : ℚ), (1 : ℚ))


/-- The probability of an event is the finite sum of its atom weights. -/
def prob (n : ℕ) (A : Finset (Option (Fin n))) : LexRat := A.sum (atomWeight n)

/-- The visible part of an event: the set of `Fin n` indices whose atom belongs to the event. -/
def visiblePart (n : ℕ) (A : Finset (Option (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun i => some i ∈ A





/-
**Closed form for event probabilities.**  The real (first) component of `prob n A` records
whether the reservoir atom `none` is present, while the infinitesimal (second) component counts the
visible atoms and subtracts `n` once if the reservoir is present.  We prove this by induction on the
finite event `A`, tracking how inserting each atom changes both the reservoir indicator, the visible
cardinality and the running sum.
-/









end InfinitesimalProbability


