-- Prove2me | solution 1 for lean_workbook_plus_77947
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:18:11.747558+00:00
-- url     : https://prove2.me/submissions/3967b7e6-19b1-434b-a7ae-e8ff02bafb7b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x < y) : ∃ r s : ℚ, x < ↑r ∧ ↑r < s ∧ s < y := by
  obtain ⟨r, hxr, hry⟩ := exists_rat_btwn h
  obtain ⟨s, hrs, hsy⟩ := exists_rat_btwn hry
  exact ⟨r, s, hxr, by exact_mod_cast hrs, hsy⟩

#print axioms solution
