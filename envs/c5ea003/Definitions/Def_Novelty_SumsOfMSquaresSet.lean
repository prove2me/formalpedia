-- Prove2me | Definitions.Def_Novelty_SumsOfMSquaresSet
-- name    : Novelty_SumsOfMSquaresSet
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:04.482483+00:00
-- url     : https://prove2.me/theorems/18fa7998-3476-4322-a4af-54118c4cfe0a
-- title:
--   Aether Catalog definitions — Novelty_SumsOfMSquaresSet
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SumsOfMSquaresSet`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SumsOfMSquaresSet.lean by skeleton subtraction
import Mathlib
/-
# Sums of `m` squares: the representation set and its structure

This file develops the elementary structural theory of the sets

`S m := { n : ℕ | n is a sum of m squares }`

that underlies the study of arithmetic sequences (such as symmetric-power
`L`-function coefficients `λ_{sym^j f}`) sampled over integers representable as a
sum of `m` squares.

The definition is the natural one:

`IsSumOfMSquares m n : ∃ v : Fin m → ℕ, (∑ i, (v i)^2) = n`.

(Working over `ℕ` loses no generality: an integer square is a natural square, so
representability as a sum of `m` integer squares agrees with the natural version.)

Main results:

* `IsSumOfMSquares.mono` — the representation sets are nested: if `n` is a sum of
  `j` squares and `j ≤ m`, then `n` is a sum of `m` squares (pad with zeros).
* `isSumOfMSquares_sq` — every perfect square is a sum of `m` squares for `m ≥ 1`.
* `setOfSumOfMSquares_infinite` — the representation set is infinite for `m ≥ 1`.
* `isSumOfMSquares_of_four_le` — **for `m ≥ 4`, *every* natural number is a sum of
  `m` squares** (Lagrange four-square theorem plus padding).  Hence `S m = ℕ` for
  `m ≥ 4`, and the only genuinely restrictive even case is `m = 2`.
* `setOfSumOfMSquares_subset` — `S j ⊆ S m` whenever `j ≤ m`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the whole "extend from `2 ≤ m ≤ 12` to all even `m ≥ 2`"
question hides a clean set-theoretic backbone.  Boldest reframing: the family of
representation sets `S m` is *monotone* in `m`, and stabilises to all of `ℕ`
already at `m = 4`.  So the sampling sets are nested, `S 2 ⊆ S 3 ⊆ ... ` and
`S m = ℕ` for `m ≥ 4`.

Experiment (Experimenter): padding a representation with zero coordinates realises
`S j ⊆ S m` for `j ≤ m`; Lagrange's four-square theorem (`Nat.sum_four_squares`)
gives `S 4 = ℕ`, and monotonicity lifts this to `S m = ℕ` for all `m ≥ 4`.
Infinitude of every `S m` (`m ≥ 1`) comes from the injection `k ↦ k²`.

Analysis (Analyst): the reframing exposes that only `m = 2` is genuinely sparse.
For `m = 3` the set omits `n ≡ 7 mod 8` (Legendre), but from `m = 4` upward there
is no restriction.  So an "all even `m ≥ 2`" statement about a sequence sampled on
`S m` is controlled entirely by the two extreme regimes `m = 2` (sparse) and
`m ≥ 4` (everything).

Critique (Critic): are the lemmas trivial?  No — `mono` needs a genuine
re-indexing (`Fin.snoc`/dependent `if`) and a sum-splitting argument, and the
four-square collapse imports a deep theorem and re-packages it as a set equality.

Synthesis (PI): the nested-sets picture is the scaffolding on which the sign-change
reduction (in `SymPowerSignChangesSumsOfSquares.lean`) rests.
-/

namespace SumsOfMSquares

open Finset

/-- `n` is a sum of `m` squares (of natural numbers). -/
def IsSumOfMSquares (m n : ℕ) : Prop :=
  ∃ v : Fin m → ℕ, (∑ i, (v i) ^ 2) = n

/-- The set of natural numbers representable as a sum of `m` squares. -/
def setOfSumOfMSquares (m : ℕ) : Set ℕ := {n | IsSumOfMSquares m n}


/-
Appending a zero coordinate: a sum of `m` squares is a sum of `m+1` squares.
-/

/-
The representation sets are nested: a sum of `j` squares is a sum of `m`
squares whenever `j ≤ m` (pad with zeros).
-/

/-
A single square is a sum of one square.
-/

/-
Every perfect square is a sum of `m` squares, for `m ≥ 1`.
-/

/-
Lagrange's four-square theorem in packaged form: every natural number is a
sum of four squares.
-/

/-
**For `m ≥ 4`, every natural number is a sum of `m` squares.**
-/

/-
For `m ≥ 4`, the representation set is all of `ℕ`.
-/


/-
The representation set is infinite for `m ≥ 1` (it contains every square).
-/

end SumsOfMSquares


