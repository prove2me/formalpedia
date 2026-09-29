-- Prove2me | solution 1 for mme_regional_target_fiber_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:48.867082+00:00
-- url     : https://prove2.me/submissions/f6ed7261-c359-4287-a51d-685d659f94f0

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_target_entropy_bounds
import Theorems.Thm_mme_regional_target_uniform_fibers
import Mathlib
open BigOperators MME.RegionRate MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3)
    (a : Address half R parent n) (ha : a ∈ target m) :
    (((target (n := n) m).filter (fun b ↦ block i b = block i a)).card : ℝ) ≤
      polynomialFactor n (R * (half + 1)) * Real.exp (jointPotential m - coarsePotential m i) := by
  classical
  have he := mme_regional_target_entropy_bounds m i a ha
  have hf := (mme_regional_target_uniform_fibers m i a ha).2
  have hb : 0 < (((target (n := n) m).image (block i)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨block i a,Finset.mem_image_of_mem _ ha⟩
  apply (mul_le_mul_iff_left₀ hb).mp
  calc
    _ = ((target (n := n) m).card : ℝ) := by exact_mod_cast (hf.trans (Nat.mul_comm _ _)).symm
    _ ≤ Real.exp (jointPotential m) := he.1
    _ = Real.exp (jointPotential m - coarsePotential m i) * Real.exp (coarsePotential m i) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (jointPotential m - coarsePotential m i) *
        (polynomialFactor n (R * (half + 1)) * (((target (n := n) m).image (block i)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left he.2.2.2 (Real.exp_pos _).le
    _ = _ := by ring
