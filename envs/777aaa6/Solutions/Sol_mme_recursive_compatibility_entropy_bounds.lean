-- Prove2me | solution 1 for mme_recursive_compatibility_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:28:07.245714+00:00
-- url     : https://prove2.me/submissions/e235c2c2-d1aa-474b-bc00-ba853cd8295f

import Theorems.Thm_mme_prescribed_cell_histogram_entropy_bounds

open BigOperators MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

theorem solution {C W G : Type*} [Fintype C] [Fintype W] [Fintype G]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ)
    (m : ℕ) (hm : 0 < m) :
    (compatibilityNumber boundary group (fun c w ↦ mu c w * m) : ℝ) ≤
      Real.exp ((m : ℝ) * potential (partCount boundary group mu)) ∧
    Real.exp ((m : ℝ) * potential (partCount boundary group mu)) ≤
      errorFactor (partCount boundary group mu) m *
        (compatibilityNumber boundary group (fun c w ↦ mu c w * m) : ℝ) := by
  classical
  have hp : partCount boundary group (fun c w ↦ mu c w * m) =
      fun s w ↦ partCount boundary group mu s w * m := by
    funext s w
    cases s with
    | inl c => rfl
    | inr g => simp only [partCount,Finset.sum_mul,ite_mul,zero_mul]
  simpa only [compatibilityNumber,hp] using
    mme_prescribed_cell_histogram_entropy_bounds (partCount boundary group mu) m hm
