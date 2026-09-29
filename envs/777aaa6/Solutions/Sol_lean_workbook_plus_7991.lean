-- Prove2me | solution 1 for lean_workbook_plus_7991
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:05.737783+00:00
-- url     : https://prove2.me/submissions/a6fa73e6-eced-40a9-ac69-625715fe5865

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.GCD.Basic

set_option autoImplicit false

theorem solution (a b : ℕ) : Nat.Coprime a b → Nat.Coprime (a * b) (a + b) := by
  intro h
  apply Nat.coprime_mul_iff_left.mpr
  constructor
  · exact Nat.coprime_self_add_right.mpr h
  · exact Nat.coprime_add_self_right.mpr h.symm
