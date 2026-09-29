-- Prove2me | solution 1 for lean_workbook_plus_45051
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T03:13:40.349909+00:00
-- url     : https://prove2.me/submissions/6b8f0eb2-cb8b-4cbc-b70c-03515c3d2132

import Mathlib

set_option autoImplicit false

namespace Workbook45051

-- Full real-floor branch from the source, not just the posted natural case.
theorem even_floor (x : ℝ) (h : Even ⌊x⌋) :
    ⌊x⌋ - 2 * ⌊x / 2⌋ = 0 := by
  obtain ⟨k, hk⟩ := h
  have hx0 := Int.floor_le x
  have hx1 := Int.lt_floor_add_one x
  rw [hk] at hx0 hx1
  push_cast at hx0 hx1
  have hh : ⌊x / 2⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith
  rw [hk, hh]
  ring

theorem full_source (b : ℕ) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ⌊2 * (b : ℝ) + y⌋ - 2 * ⌊(2 * (b : ℝ) + y) / 2⌋ = 0 := by
  apply even_floor
  have he : ⌊2 * (b : ℝ) + y⌋ = 2 * (b : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  rw [he]
  exact even_two_mul _

end Workbook45051

theorem solution (x : ℕ) (h₀ : Even x) :
    (x : ℤ) - 2 * (x / 2) = 0 := by
  obtain ⟨k, rfl⟩ := h₀
  push_cast
  omega
