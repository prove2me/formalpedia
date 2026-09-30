-- Prove2me | solution 1 for lean_workbook_plus_57415
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:35:05.049941+00:00
-- url     : https://prove2.me/submissions/6ee32d23-0ce1-481c-9e65-1a2625c227a0

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem one_coordinate (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hs : x + y + z = 1)
    (hr : 1 / x + 1 / y + 1 / z = 1) :
    x = 1 ∨ y = 1 ∨ z = 1 := by
  have hp : (x - 1) * (y - 1) * (z - 1) = 0 := by
    field_simp [hx, hy, hz] at hr
    nlinarith [hr]
  rcases mul_eq_zero.mp hp with hp | hz
  · rcases mul_eq_zero.mp hp with hx | hy
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

theorem reciprocal_system_classification (x y z : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x + y + z = 1 ∧ 1 / x + 1 / y + 1 / z = 1) ↔
      (x = 1 ∧ z = -y) ∨ (y = 1 ∧ z = -x) ∨ (z = 1 ∧ y = -x) := by
  constructor
  · rintro ⟨hs, hr⟩
    rcases one_coordinate x y z hx hy hz hs hr with h | h | h
    · exact Or.inl ⟨h, by linarith⟩
    · exact Or.inr (Or.inl ⟨h, by linarith⟩)
    · exact Or.inr (Or.inr ⟨h, by linarith⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals constructor
    all_goals ring

theorem solution (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x + y + z = 1) (h : 1 / x + 1 / y + 1 / z = 1) :
    x = 1 ∨ y = 1 ∨ z = 1 :=
  one_coordinate x y z hx hy hz hxy h
