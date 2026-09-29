-- Prove2me | solution 1 for HilbertChess.exists_safe_row
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:20:12.016873+00:00
-- url     : https://prove2.me/submissions/480153be-8d4c-4f10-a3d4-64b5beb2ad88

import Mathlib
import Definitions.Def_Geometry_HilbertChessLines
open HilbertChess in
theorem solution (S : List Line) : ∃ k : ℤ, ∀ L ∈ S, L.a = 0 → ¬ L.covers (0, k) := by
  -- a row above every horizontal line's intercept
  set A : ℤ := (S.map fun L => |L.c|).sum with hA
  refine ⟨A + 1, fun L hL ha hcov => ?_⟩
  have hcov' : L.a * 0 + L.b * (A + 1) = L.c := hcov
  have hb : L.b ≠ 0 := L.nondeg.resolve_left (not_not.mpr ha)
  have hA0 : 0 ≤ A := List.sum_nonneg (by
    intro z hz
    obtain ⟨L', _, rfl⟩ := List.mem_map.mp hz
    exact abs_nonneg _)
  have hc : |L.c| ≤ A := List.single_le_sum (by
      intro z hz
      obtain ⟨L', _, rfl⟩ := List.mem_map.mp hz
      exact abs_nonneg _) _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
  -- `|A + 1| ≤ |b (A + 1)| = |c| ≤ A`
  have h1 : |A + 1| ≤ |L.b * (A + 1)| := by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs hb)
  rw [mul_zero, zero_add] at hcov'
  rw [hcov', abs_of_pos (by linarith : (0 : ℤ) < A + 1)] at h1
  linarith
