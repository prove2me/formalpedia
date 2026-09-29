-- Prove2me | Theorems.Thm_lean_workbook_plus_15427
-- name    : lean_workbook_plus_15427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1eaccc82-62e4-4ad8-8772-ea58b1cda75d
-- statement:
--   Let $a,\ b,\ c$ be real numbers such that $a+b+c=0$ . Prove that $a^2b^2+b^2c^2+c^2a^2+6abc\geq -3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15427 (a b c : ℝ) (hab : a + b + c = 0) : a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 + 6 * a * b * c ≥ -3   :=  by sorry
