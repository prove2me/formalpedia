-- Prove2me | solution 1 for BonferroniMarginals.sq_spread_le_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:26:11.319809+00:00
-- url     : https://prove2.me/submissions/13f84449-123e-4a84-8423-b94eb7c46bb2

-- Sol generated from MachineLearning/BonferroniMarginals/Stability.lean
import Mathlib
import Definitions.Def_MachineLearning_BonferroniMarginals_Core
import Definitions.Def_MachineLearning_BonferroniMarginals_HigherOrderNecessity
import Definitions.Def_MachineLearning_BonferroniMarginals_Stability
import Theorems.Thm_BonferroniMarginals_lagrange_identity

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



lemma csGap_nonneg (I : Finset ι) (A : ι → Finset Ω) : 0 ≤ csGap I A := by
  have hL := lagrange_identity (cover I A) (fun x => (mult I A x : ℤ))
  have hnn : (0:ℤ) ≤ ∑ x ∈ cover I A, ∑ y ∈ cover I A,
      ((mult I A x : ℤ) - (mult I A y : ℤ)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [← hL] at hnn
  rw [csGap]
  linarith






open BonferroniMarginals in
theorem solution(I : Finset ι) (A : ι → Finset Ω) {x y : Ω}
    (hx : x ∈ cover I A) (hy : y ∈ cover I A) :
    ((mult I A x : ℤ) - (mult I A y : ℤ)) ^ 2 ≤ csGap I A := by
  classical
  set U := cover I A with hU
  set f : Ω → ℤ := fun z => (mult I A z : ℤ) with hf
  have hL := lagrange_identity U f
  by_cases hxy : x = y
  · subst hxy
    simpa using csGap_nonneg I A
  -- restrict the double sum to the two-point subset `{x, y}`
  have hsub : ({x, y} : Finset Ω) ⊆ U := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hinner : ∀ z ∈ U, ∑ w ∈ ({x, y} : Finset Ω), (f z - f w) ^ 2
      ≤ ∑ w ∈ U, (f z - f w) ^ 2 := by
    intro z _
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => sq_nonneg _)
  have houter : ∑ z ∈ ({x, y} : Finset Ω), ∑ w ∈ ({x, y} : Finset Ω), (f z - f w) ^ 2
      ≤ ∑ z ∈ U, ∑ w ∈ U, (f z - f w) ^ 2 := by
    calc ∑ z ∈ ({x, y} : Finset Ω), ∑ w ∈ ({x, y} : Finset Ω), (f z - f w) ^ 2
        ≤ ∑ z ∈ U, ∑ w ∈ ({x, y} : Finset Ω), (f z - f w) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun z _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ ∑ z ∈ U, ∑ w ∈ U, (f z - f w) ^ 2 := Finset.sum_le_sum hinner
  have htwo : ∑ z ∈ ({x, y} : Finset Ω), ∑ w ∈ ({x, y} : Finset Ω), (f z - f w) ^ 2
      = 2 * (f x - f y) ^ 2 := by
    rw [Finset.sum_pair hxy, Finset.sum_pair hxy, Finset.sum_pair hxy]
    ring
  rw [htwo] at houter
  rw [csGap]
  linarith [hL, houter]
