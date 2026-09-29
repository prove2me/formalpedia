-- Prove2me | solution 1 for BonferroniMarginals.regular_of_gap_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:29:00.539253+00:00
-- url     : https://prove2.me/submissions/eea30fc1-ee38-4b02-8a09-7ef134cfb83c

-- Sol generated from MachineLearning/BonferroniMarginals/Stability.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_Rigidity
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability
import Theorems.Thm_BonferroniMarginals_sq_spread_le_gap

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
theorem solution(I : Finset ι) (A : ι → Finset Ω) (h : csGap I A = 0) :
    ∃ d, IsRegularCover I A d := by
  classical
  rcases (cover I A).eq_empty_or_nonempty with hemp | ⟨x0, hx0⟩
  · exact ⟨0, fun x hx => absurd hx (by simp [hemp])⟩
  · refine ⟨mult I A x0, fun x hx => ?_⟩
    have hsq := sq_spread_le_gap I A hx hx0
    rw [h] at hsq
    have : ((mult I A x : ℤ) - (mult I A x0 : ℤ)) ^ 2 = 0 :=
      le_antisymm hsq (sq_nonneg _)
    have hzero : (mult I A x : ℤ) - (mult I A x0 : ℤ) = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have : (mult I A x : ℤ) = (mult I A x0 : ℤ) := by linarith
    exact_mod_cast this
