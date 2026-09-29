-- Prove2me | solution 1 for Cryptography.IsogenySIDH.quotient_fiber_classification
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:01:33.442795+00:00
-- url     : https://prove2.me/submissions/1ec4b03b-23f2-4094-9a0c-4ed51289015d

import Mathlib
import Definitions.Def_Cryptography_AbstractAlgebra_IsogenyFoundations
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery

variable {K : Type*} [Field K]

theorem solution {x z : K} (hx : x ≠ 0) (hz : z ≠ 0)
    (h : x + x⁻¹ = z + z⁻¹) : x = z ∨ x * z = 1 := by
  -- Clear denominators algebraically
  have hxZ : x * z ≠ 0 := mul_ne_zero hx hz
  have clear :
      x * z * (x + x⁻¹) = x * z * (z + z⁻¹) := by rw [h]
  have L : x * z * (x + x⁻¹) = x ^ 2 * z + z := by
    calc
      x * z * (x + x⁻¹) = x * z * x + x * z * x⁻¹ := by ring
      _ = x ^ 2 * z + z * (x * x⁻¹) := by ring
      _ = x ^ 2 * z + z := by simp [hx]
  have R : x * z * (z + z⁻¹) = x * z ^ 2 + x := by
    calc
      x * z * (z + z⁻¹) = x * z * z + x * z * z⁻¹ := by ring
      _ = x * z ^ 2 + x * (z * z⁻¹) := by ring
      _ = x * z ^ 2 + x := by simp [hz]
  have heq : x ^ 2 * z + z = x * z ^ 2 + x := by
    rw [← L, ← R, clear]
  have h0 : (x - z) * (x * z - 1) = 0 := by
    have : x ^ 2 * z + z - (x * z ^ 2 + x) = 0 := by rw [heq]; abel
    convert this using 1; ring
  rcases mul_eq_zero.mp h0 with hxz | hp
  · left; exact eq_of_sub_eq_zero hxz
  · right; exact eq_of_sub_eq_zero hp
