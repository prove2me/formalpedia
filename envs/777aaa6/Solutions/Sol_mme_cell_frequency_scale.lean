-- Prove2me | solution 1 for mme_cell_frequency_scale
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:34:23.422295+00:00
-- url     : https://prove2.me/submissions/46eee345-00dc-455b-bd2f-7f5204394992

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

/-- Replicating every occurrence preserves each normalized child profile. -/
theorem solution
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

#print axioms solution
