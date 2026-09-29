-- Prove2me | solution 1 for mme_entropy_penalty_of_positive_reference
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:56:30.712759+00:00
-- url     : https://prove2.me/submissions/9466b8ba-cd16-4dbf-a72a-cd52b4fb90da

import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem entropy_cross_bound {C : Type*} [Fintype C]
    (p q : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hm : ∑ c, p c = 1)
    (hq : ∀ c, 0 < q c) (hqm : ∑ c, q c = 1) :
    entropy p ≤ -(∑ c, p c * Real.log (q c)) := by
  have ht (c : C) : Real.negMulLog (p c) ≤ q c-p c-p c*Real.log (q c) := by
    by_cases hz : p c = 0
    · simp [hz,(hq c).le]
    have hp' := lt_of_le_of_ne (hp c) (Ne.symm hz)
    have hl := Real.log_le_sub_one_of_pos (div_pos (hq c) hp')
    rw [Real.log_div (hq c).ne' hz] at hl
    have hh := mul_le_mul_of_nonneg_left hl (hp c)
    rw [mul_sub,mul_sub,mul_div_cancel₀ _ hz,mul_one] at hh
    unfold Real.negMulLog
    linarith
  have hs := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset C)) ↦ ht c)
  simpa only [Finset.sum_sub_distrib,hm,hqm,sub_self,zero_sub] using hs

theorem solution {degree : ℕ} {bounds : Fin 3 → ℕ}
    (alpha q : Split degree bounds → ℝ)
    (hp : ∀ c, 0 ≤ alpha c) (hm : ∑ c, alpha c = 1)
    (hq : ∀ c, 0 < q c) (hqm : ∑ c, q c = 1)
    (hmoment : ∀ rho ∈ SameMarginalDistributions alpha,
      (∑ c, rho c * Real.log (q c)) = ∑ c, alpha c * Real.log (q c)) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ c, alpha c * Real.log (q c)) - entropy alpha := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hself : alpha ∈ SameMarginalDistributions alpha := ⟨hp,hm,fun _ _ ↦ rfl⟩
  have hs : sSup (mme_modern_entropyBits '' SameMarginalDistributions alpha) ≤
      -(∑ c, alpha c * Real.log (q c))/Real.log 2 := by
    apply csSup_le ⟨mme_modern_entropyBits alpha,Set.mem_image_of_mem _ hself⟩
    rintro z ⟨rho,hr,rfl⟩
    change entropy rho/Real.log 2 ≤ _
    apply div_le_div_of_nonneg_right _ hl.le
    rw [← hmoment rho hr]
    exact entropy_cross_bound rho q hr.1 hr.2.1 hq hqm
  have hb := (le_div_iff₀ hl).mp hs
  have he : Real.log 2*mme_modern_entropyBits alpha = entropy alpha := by
    unfold mme_modern_entropyBits entropy
    field_simp
  unfold entropyPenalty
  rw [mul_sub,he]
  linarith
