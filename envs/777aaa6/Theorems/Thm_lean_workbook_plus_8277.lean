-- Prove2me | Theorems.Thm_lean_workbook_plus_8277
-- name    : lean_workbook_plus_8277
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3a611c01-940b-4302-9e1a-049088b61d85
-- statement:
--   If none of the three numbers is divisible by \(5\), prove that \(a^3b - ab^3\) is divisible by \(10\) by considering cases where \(a\) and \(b\) are congruent to \(0\) modulo \(5\), or congruent to \(1\) and \(4\), or congruent to \(2\) and \(3\) modulo \(5\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8277 : ∀ a b : ℤ, ¬ 5 ∣ a ∧ ¬ 5 ∣ b → a^3 * b - a * b^3 ≡ 0 [ZMOD 10]   :=  by sorry
