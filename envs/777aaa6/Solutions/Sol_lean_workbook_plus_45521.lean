-- Prove2me | solution 1 for lean_workbook_plus_45521
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:20:18.105677+00:00
-- url     : https://prove2.me/submissions/b101344d-3746-47a9-8a25-5c967ace5474

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y z : ℤ) (h : x * y * (x ^ 2 - y ^ 2) + y * z * (y ^ 2 - z ^ 2) + z * x * (z ^ 2 - x ^ 2) = 1) : (x = 0 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = -1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 0) ∨ (x = -1 ∧ y = 0 ∧ z = 0) ∨ (x = 1 ∧ y = -1 ∧ z = 0) ∨ (x = -1 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 0 ∧ y = 0 ∧ z = -1) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨ (x = -1 ∧ y = 0 ∧ z = -1) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨ (x = 0 ∧ y = -1 ∧ z = -1)   := by
  have even_pair (a b : ℤ) : 2 ∣ a * b * (a ^ 2 - b ^ 2) := by
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    apply Int.dvd_of_emod_eq_zero
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Int.mul_emod, Int.sub_emod, pow_two, ha, hb]
  have hd := dvd_add (dvd_add (even_pair x y) (even_pair y z)) (even_pair z x)
  rw [h] at hd
  norm_num at hd
