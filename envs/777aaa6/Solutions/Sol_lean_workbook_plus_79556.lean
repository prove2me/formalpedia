-- Prove2me | solution 1 for lean_workbook_plus_79556
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:44.528545+00:00
-- url     : https://prove2.me/submissions/ab09f2eb-feec-4adb-a4f9-06d2139c4f8f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) (h₁ : a ≥ b ∧ b ≥ c ∧ c ≥ a) (k : ℕ) :
    (a - b)^(2 * k + 1) + (b - c)^(2 * k + 1) + (c - a)^(2 * k + 1) ≤ 0 := by
  obtain ⟨hab, hbc, hca⟩ := h₁
  have hab' : a = b := by linarith
  have hbc' : b = c := by linarith
  subst a
  subst b
  simp
