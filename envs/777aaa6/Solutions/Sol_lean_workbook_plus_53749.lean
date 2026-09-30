-- Prove2me | solution 1 for lean_workbook_plus_53749
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:37:13.345146+00:00
-- url     : https://prove2.me/submissions/196f500a-0e7a-43c6-9aea-a00638c7efb7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem constrained_reciprocal_gap (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (b + c) / a + (c + a) / b = 12) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) - 77 / 5 =
      7 * (a - b) ^ 2 / (5 * c * (a + b)) := by
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hc0 := ne_of_gt hc
  have hs0 : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hpoly : (b + c) * b + (c + a) * a = 12 * (a * b) := by
    field_simp [ha0, hb0] at h
    nlinarith [h]
  have ht : (a + b + c) * (1 / a + 1 / b + 1 / c) =
      15 + (a + b) / c := by
    calc
      _ = 3 + ((b + c) / a + (c + a) / b) + (a + b) / c := by
        field_simp
        <;> ring
      _ = _ := by rw [h]; ring
  rw [ht]
  field_simp [hc0, hs0]
  nlinarith [hpoly]

theorem constrained_reciprocal_equality (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (b + c) / a + (c + a) / b = 12) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) = 77 / 5 ↔
      a = b ∧ c = 5 * a := by
  constructor
  · intro he
    have hg := constrained_reciprocal_gap a b c ha hb hc h
    rw [he, sub_self] at hg
    have hz : 7 * (a - b) ^ 2 = 0 :=
      (div_eq_zero_iff).mp hg.symm |>.resolve_right (by positivity)
    have hab : a = b := by nlinarith [sq_nonneg (a - b)]
    subst b
    have hp := h
    field_simp [ne_of_gt ha] at hp
    have hprod : a * (c - 5 * a) = 0 := by nlinarith [hp]
    have hec : c - 5 * a = 0 :=
      (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
    exact ⟨rfl, by linarith⟩
  · rintro ⟨hab, hca⟩
    have hg := constrained_reciprocal_gap a b c ha hb hc h
    rw [hab, sub_self] at hg
    norm_num at hg
    rw [hab]
    simpa only [one_div, sub_eq_zero] using hg

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (b + c) / a + (c + a) / b = 12) :
    (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 77 / 5 := by
  have hn : 0 ≤ 7 * (a - b) ^ 2 / (5 * c * (a + b)) := by positivity
  linarith [constrained_reciprocal_gap a b c ha hb hc h]

#print axioms solution
#print axioms constrained_reciprocal_gap
#print axioms constrained_reciprocal_equality
