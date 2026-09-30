-- Prove2me | solution 1 for lean_workbook_plus_79819
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:08:18.853177+00:00
-- url     : https://prove2.me/submissions/a02f13e8-219e-4fef-86a7-a606a546d178

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem solution (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (h : 1 / p + 1 / q = 1) :
    1 / (p * (p + 1)) + 1 / (q * (q + 1)) ≥ 1 / 3 := by
  have hp0 := hp.ne'
  have hq0 := hq.ne'
  have hp1 : p + 1 ≠ 0 := ne_of_gt (by positivity)
  have hq1 : q + 1 ≠ 0 := ne_of_gt (by positivity)
  have hpq : p + q = p * q := by
    field_simp at h
    nlinarith
  have hs : 4 ≤ p + q := by
    nlinarith [sq_nonneg (p - q)]
  have hden : 0 < 2 * (p + q) + 1 := by positivity
  have hd : p * (p + 1) * q * (q + 1) = (p + q) * (2 * (p + q) + 1) := by
    calc
      _ = (p * q) * (p * q + p + q + 1) := by ring
      _ = _ := by rw [← hpq]; ring
  have hn : q * (q + 1) + p * (p + 1) = (p + q) * (p + q - 1) := by
    nlinarith
  have heq : 1 / (p * (p + 1)) + 1 / (q * (q + 1)) =
      (p + q - 1) / (2 * (p + q) + 1) := by
    field_simp
    rw [hd, hn]
    ring
  rw [heq]
  apply (le_div_iff₀ hden).mpr
  linarith

#print axioms solution
