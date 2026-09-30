-- Prove2me | solution 1 for lean_workbook_plus_58417
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:25:38.5926+00:00
-- url     : https://prove2.me/submissions/f15bfd1e-266b-47f0-8a35-0cdcbd084a15

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace FourCycleCube

theorem gap (x y z t : ℝ) :
    2 * (2 - (x * (1 - y) + y * (1 - z) + z * (1 - t) + t * (1 - x))) =
      (x + z) * (y + t) + (2 - x - z) * (2 - y - t) := by ring

theorem bound (x y z t : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - t) + t * (1 - x) ≤ 2 := by
  have h₁ := mul_nonneg (add_nonneg hx.1 hz.1) (add_nonneg hy.1 ht.1)
  have h₂ := mul_nonneg (show 0 ≤ 2 - x - z by linarith [hx.2, hz.2])
    (show 0 ≤ 2 - y - t by linarith [hy.2, ht.2])
  linarith [gap x y z t]

theorem equality (x y z t : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - t) + t * (1 - x) = 2 ↔
      (x = 0 ∧ y = 1 ∧ z = 0 ∧ t = 1) ∨ (x = 1 ∧ y = 0 ∧ z = 1 ∧ t = 0) := by
  constructor
  · intro he
    have h₁ := mul_nonneg (add_nonneg hx.1 hz.1) (add_nonneg hy.1 ht.1)
    have h₂ := mul_nonneg (show 0 ≤ 2 - x - z by linarith [hx.2, hz.2])
      (show 0 ≤ 2 - y - t by linarith [hy.2, ht.2])
    have hp : (x + z) * (y + t) = 0 := by linarith [gap x y z t]
    rcases mul_eq_zero.mp hp with hxz | hyt
    · have hx0 : x = 0 := by linarith [hx.1, hz.1]
      have hz0 : z = 0 := by linarith [hx.1, hz.1]
      subst x
      subst z
      refine Or.inl ⟨rfl, ?_, rfl, ?_⟩ <;> nlinarith [hy.2, ht.2]
    · have hy0 : y = 0 := by linarith [hy.1, ht.1]
      have ht0 : t = 0 := by linarith [hy.1, ht.1]
      subst y
      subst t
      refine Or.inr ⟨?_, rfl, ?_, rfl⟩ <;> nlinarith [hx.2, hz.2]
  · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> ring

end FourCycleCube

theorem solution (x y z t : ℝ) (hx : x ∈ Set.Icc 0 1) (hy : y ∈ Set.Icc 0 1)
    (hz : z ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    x * (1 - y) + y * (1 - z) + z * (1 - t) + t * (1 - x) ≤ 2 :=
  FourCycleCube.bound x y z t hx hy hz ht
