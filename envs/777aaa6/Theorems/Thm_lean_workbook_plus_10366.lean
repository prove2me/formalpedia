-- Prove2me | Theorems.Thm_lean_workbook_plus_10366
-- name    : lean_workbook_plus_10366
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c23c5a5b-9005-435a-9490-63197a9a69c8
-- statement:
--   If $a,b$ are non-negative reals, such that $a+b=2$ , prove that $a^{4}+b^{4}\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10366 (a b : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ a + b = 2) : a^4 + b^4 ≥ 2   :=  by sorry
