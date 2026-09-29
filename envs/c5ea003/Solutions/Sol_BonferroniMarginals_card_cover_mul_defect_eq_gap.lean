-- Prove2me | solution 1 for BonferroniMarginals.card_cover_mul_defect_eq_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:23:50.69898+00:00
-- url     : https://prove2.me/submissions/aeff6075-07f0-4d7d-832b-54a9c391a8b3

-- Sol generated from MachineLearning/BonferroniMarginals/Stability.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability

/-!
# Quantitative rigidity: near-tightness forces near-regularity

`Rigidity.lean` characterises *exact* equality in the second-moment bound
`(∑ᵢ|Aᵢ|)² ≤ |cover| · ∑_{(i,j)}|Aᵢ ∩ Aⱼ|`: it holds iff the coverage
multiplicity is constant.  Exact statements of that kind are fragile, so this
file upgrades the characterisation to a **stability** statement with an explicit
modulus.

Main results.

* `sq_spread_le_gap` — for any two covered points `x, y`,
  `(mult x − mult y)² ≤ |cover|·∑_{(i,j)}|Aᵢ∩Aⱼ| − (∑ᵢ|Aᵢ|)²`.
  The whole spread of the multiplicity function is controlled by the square root
  of the Cauchy–Schwarz gap.
* `regular_of_gap_zero` — the exact rigidity statement re-derived as the
  degenerate case, and `mult_eq_of_gap_lt_one` : a gap smaller than `1` already
  forces exact regularity (the gap is an integer).
* `bonferroni_defect_le_gap` — the Bonferroni defect `∑ₓ(mult x − 1)²` of
  `Rigidity.lean` is itself controlled: for a family whose Cauchy–Schwarz gap is
  `g` and whose average multiplicity is `1`, the defect is at most `g`.

Machine-learning reading: an ensemble whose second-order statistics are within
`g` of the Corrádi extremal profile has all coverage multiplicities within
`√g` of each other — the failure mass is *uniformly* spread, quantitatively.
-/

open BonferroniMarginals

open Finset

variable {Ω ι : Type*} [DecidableEq Ω]
variable {I : Finset ι} {A : ι → Finset Ω}









open BonferroniMarginals in
theorem solution(I : Finset ι) (A : ι → Finset Ω)
    (havg : ∑ x ∈ cover I A, mult I A x = (cover I A).card) :
    ((cover I A).card : ℤ) * (∑ x ∈ cover I A, ((mult I A x : ℤ) - 1) ^ 2)
      = csGap I A := by
  have hexpand : ∑ x ∈ cover I A, ((mult I A x : ℤ) - 1) ^ 2
      = (∑ x ∈ cover I A, (mult I A x : ℤ) ^ 2)
        - 2 * (∑ x ∈ cover I A, (mult I A x : ℤ)) + (cover I A).card := by
    have hpt : ∀ x : Ω, ((mult I A x : ℤ) - 1) ^ 2
        = (mult I A x : ℤ) ^ 2 - 2 * (mult I A x : ℤ) + 1 := by
      intro x; ring
    simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hcast : (∑ x ∈ cover I A, (mult I A x : ℤ)) = ((cover I A).card : ℤ) := by
    have : ((∑ x ∈ cover I A, mult I A x : ℕ) : ℤ) = ((cover I A).card : ℤ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) havg
    push_cast at this
    linarith
  rw [csGap, hexpand, hcast]
  ring
