-- Prove2me | solution 1 for mme_global_CW_canonical_subexponential_repair
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T10:26:18.497705+00:00
-- url     : https://prove2.me/submissions/7d875d72-305e-4389-962b-9546fe5dc350

import Definitions.Def_mme_global_CW_histogram_frame
import Theorems.Thm_mme_global_CW_histogram_capacity_bound
import Theorems.Thm_mme_square_scale_logarithmic_repair_cost
open BigOperators MME MME.RecursiveYZ MME.GlobalCW
set_option autoImplicit false

theorem solution (C : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∃ hk : 1 < k,
      ∀ {ell M : ℕ} (D : HistogramFrame ell M) (mu : D.AdmissibleProfile),
      M ≤ C * k ^ 2 →
      ((D.stage mu k hk).repairExponent : ℝ) * Real.log 8 < delta * (k : ℝ) ^ 2 := by
  obtain ⟨k0,hk0⟩ := mme_square_scale_logarithmic_repair_cost (3*C) delta hdelta
  refine ⟨k0,fun k hk ↦ ?_⟩
  have hk1 : 1 < k := (hk0 k hk 0 (Nat.zero_le _)).1
  refine ⟨hk1,?_⟩
  intro ell M D mu hsize
  have hcap : D.capacity mu.val ≤ 7 ^ ((3*C) * k ^ 2) := by
    apply (mme_global_CW_histogram_capacity_bound D mu.val).trans
    apply Nat.pow_le_pow_right (by omega)
    calc
      3*M ≤ 3*(C*k^2) := Nat.mul_le_mul_left 3 hsize
      _ = (3*C)*k^2 := by ring
  have h := (hk0 k hk (D.capacity mu.val) hcap).2.2
  simpa only [HistogramFrame.stage,Real.log_pow] using h
