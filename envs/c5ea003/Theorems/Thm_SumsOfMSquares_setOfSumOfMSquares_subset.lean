-- Prove2me | Theorems.Thm_SumsOfMSquares_setOfSumOfMSquares_subset
-- name    : SumsOfMSquares.setOfSumOfMSquares_subset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:37:49.556652+00:00
-- url     : https://prove2.me/theorems/a11c601e-cdb2-476b-aa7b-676d688b2d4b
-- title:
--   Nesting at the level of sets: `S j ⊆ S m` when `j ≤ m`.
-- statement:
--   Nesting at the level of sets: `S j ⊆ S m` when `j ≤ m`.
--
--   ```lean
--   theorem SumsOfMSquares.setOfSumOfMSquares_subset{j m : ℕ} (hjm : j ≤ m) :
--       setOfSumOfMSquares j ⊆ setOfSumOfMSquares m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SumsOfMSquaresSet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SumsOfMSquaresSet.lean#L125

-- Thm stub generated from Novelty/SumsOfMSquaresSet.lean
import Mathlib
import Definitions.Def_Novelty_SumsOfMSquaresSet
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

open SumsOfMSquares

open Finset




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

theorem SumsOfMSquares.setOfSumOfMSquares_subset{j m : ℕ} (hjm : j ≤ m) :
    setOfSumOfMSquares j ⊆ setOfSumOfMSquares m := by sorry
