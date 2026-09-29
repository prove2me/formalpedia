-- Prove2me | solution 1 for lean_workbook_plus_73903
-- status  : ACCEPTED   (prove)
-- author  : @Henry Yuen
-- created : 2026-03-11T17:26:33.820782+00:00
-- url     : https://prove2.me/submissions/4abb8af9-8648-4fd0-9610-62f6c0293657

import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

theorem solution (a b : ℝ) : (a + b) ^ 2 - 2 * a * b = a ^ 2 + b ^ 2 := by
  ring

-- Auto-generated type check: solution must match the target
theorem _type_check_target (a b : ℝ) : (a + b) ^ 2 - 2 * a * b = a ^ 2 + b ^ 2   := by apply solution
