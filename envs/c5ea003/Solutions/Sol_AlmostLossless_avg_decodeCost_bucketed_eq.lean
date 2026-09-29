-- Prove2me | solution 1 for AlmostLossless.avg_decodeCost_bucketed_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:28:56.20729+00:00
-- url     : https://prove2.me/submissions/3347f059-72ff-4cec-ba75-667fd77af60d

-- Sol generated from Logic/AlmostLossless/Complexity.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme
import Theorems.Thm_AlmostLossless_avg_collisionCount_eq
import Theorems.Thm_AlmostLossless_decodeCost_bucketed_self

/-!
# Decoder complexity: an exact expected cost and a universal lower bound

The rate side of almost-lossless compression is settled by `Core`; this file is
about the *time* side, which the research thread identifies as the real
obstacle.

* `AlmostLossless.avg_decodeCost_bucketed_eq` — for a **pairwise independent**
  hash family the expected number of candidate tests performed by the bucketed
  decoder on a typical word is *exactly* `1 + (|T|-1)/m₁`, matching the
  numerical measurements (Section 4 of `ComputationalEvidence.md`) to the digit.
  So the upper bound `avg_decodeCost_bucketed_le` cannot be improved for this
  class of families.

* `AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost` — a *universal*
  lower bound: for **every** scan scheme and every seed, the total decoding work
  over the typical set is at least `|T|²/|M|` (Cauchy–Schwarz over the buckets),
  and each individual decoding costs at least one test.  Hence no scheme with
  `m` codewords can decode a typical set of size `t` in less than `t/m` expected
  tests: rate and decoding time obey a hyperbolic trade-off.

Together these pin the bucketed decoder to within an additive `1` of optimal.
-/

open AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## Exact expected work for pairwise independent families -/



variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]



/-! ## A universal lower bound on decoder work -/

variable [Fintype M]






open AlmostLossless in
omit [DecidableEq M₂] in
theorem solution[Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
    [Fintype M₁] [Nonempty M₁] (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
    (hpi : PairwiseIndependent h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
    (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
        ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
      = 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by
  have hA : (0 : ℚ) < (Fintype.card A₁ : ℚ) := by exact_mod_cast Fintype.card_pos (α := A₁)
  have hterm : ∀ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
      ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)
      = 1 + (collisionCount h₁ T a₁ x : ℚ) := by
    intro a₁
    rw [decodeCost_bucketed_self T h₁ h₂ a₁ a₂ hx]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun a₁ _ => hterm a₁), Finset.sum_add_distrib]
  have hone : ∑ _a₁ : A₁, (1 : ℚ) = (Fintype.card A₁ : ℚ) := by simp
  rw [hone, add_div, div_self (ne_of_gt hA), avg_collisionCount_eq hpi T x]
