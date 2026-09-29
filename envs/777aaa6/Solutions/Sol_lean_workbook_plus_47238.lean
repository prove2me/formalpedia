-- Prove2me | solution 1 for lean_workbook_plus_47238
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:19:58.992032+00:00
-- url     : https://prove2.me/submissions/35043a4c-3aaa-4b9e-9c31-e084973488f3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (1 / (2 * x + 1) + 1 / (2 * y + 1)) ≥ 2 / (x * y + 2) := by
  have hg : 0 ≤ x*y*(x+y-3)+1 := by
    by_cases hs : 3 ≤ x+y
    · have hp := mul_nonneg (mul_nonneg hx hy) (sub_nonneg.mpr hs)
      linarith
    · have hs' : 0 ≤ 3-(x+y) := by linarith
      have ht : 0 ≤ x+y+1 := by positivity
      nlinarith [mul_nonneg ht (sq_nonneg (x+y-2)), mul_nonneg hs' (sq_nonneg (x-y))]
  have h₁ : 0 < 2*x+1 := by positivity
  have h₂ : 0 < 2*y+1 := by positivity
  have h₃ : 0 < x*y+2 := by positivity
  have hd : 0 < (2*x+1)*(2*y+1)*(x*y+2) := by positivity
  have he₁ : (1/(2*x+1)+1/(2*y+1))*((2*x+1)*(2*y+1)*(x*y+2)) = (2*x+2*y+2)*(x*y+2) := by
    field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃] <;> ring
  have he₂ : (2/(x*y+2))*((2*x+1)*(2*y+1)*(x*y+2)) = 2*(2*x+1)*(2*y+1) := by
    field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃] <;> ring
  apply (mul_le_mul_iff_left₀ hd).mp
  rw [he₁, he₂]
  nlinarith
