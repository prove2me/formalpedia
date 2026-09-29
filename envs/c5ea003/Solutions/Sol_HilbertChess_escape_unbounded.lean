-- Prove2me | solution 1 for HilbertChess.escape_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:15:48.164581+00:00
-- url     : https://prove2.me/submissions/231d01b1-1f07-434a-a91d-c9cf98e1f3d8

import Mathlib
import Definitions.Def_Geometry_HilbertChessLines
open HilbertChess in
theorem solution (S : List Line) (N : ℤ) : ∃ q : Square, safe S q ∧ N < q.1 := by
  -- go far to the right, then far up, beyond every line's reach
  set A : ℤ := (S.map fun L => |L.c|).sum with hA
  set x : ℤ := |N| + A + 1 with hx
  set B : ℤ := (S.map fun L => |L.c - L.a * x|).sum with hB
  set y : ℤ := B + 1 with hy
  have hA0 : 0 ≤ A := List.sum_nonneg (by
    intro z hz
    obtain ⟨L', _, rfl⟩ := List.mem_map.mp hz
    exact abs_nonneg _)
  have hB0 : 0 ≤ B := List.sum_nonneg (by
    intro z hz
    obtain ⟨L', _, rfl⟩ := List.mem_map.mp hz
    exact abs_nonneg _)
  refine ⟨(x, y), ?_, ?_⟩
  · rintro ⟨L, hL, hcov⟩
    have hcov' : L.a * x + L.b * y = L.c := hcov
    have hc : |L.c| ≤ A := List.single_le_sum (by
        intro z hz
        obtain ⟨L', _, rfl⟩ := List.mem_map.mp hz
        exact abs_nonneg _) _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
    have hr : |L.c - L.a * x| ≤ B := List.single_le_sum (by
        intro z hz
        obtain ⟨L', _, rfl⟩ := List.mem_map.mp hz
        exact abs_nonneg _) _ (List.mem_map.mpr ⟨L, hL, rfl⟩)
    have hxpos : 0 < x := by have := abs_nonneg N; linarith
    by_cases hb : L.b = 0
    · -- a vertical line would need `|a·x| = |c|`, but `|a·x| ≥ x > |c|`
      have ha : L.a ≠ 0 := L.nondeg.resolve_right (not_not.mpr hb)
      rw [hb, zero_mul, add_zero] at hcov'
      have h1 : |x| ≤ |L.a * x| := by
        rw [abs_mul]
        exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs ha)
      rw [hcov', abs_of_pos hxpos] at h1
      have := abs_nonneg N
      linarith
    · -- otherwise `|y| ≤ |b·y| = |c - a·x| ≤ B < y`
      have h1 : |y| ≤ |L.b * y| := by
        rw [abs_mul]
        exact le_mul_of_one_le_left (abs_nonneg _) (Int.one_le_abs hb)
      have h2 : L.b * y = L.c - L.a * x := by linarith
      rw [h2, abs_of_pos (by linarith : (0 : ℤ) < y)] at h1
      linarith
  · show N < x
    have := le_abs_self N
    linarith
