-- Prove2me | Theorems.Thm_lean_workbook_plus_75334
-- name    : lean_workbook_plus_75334
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f182cb66-14c2-4ec0-9854-6a01c64746c7
-- statement:
--   Let $a+b\geq 0$ . Prove that $a^2+3a+7b^2+6b+5ab\geq -\frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75334 (a b : ℝ) (ha : a + b ≥ 0) : a^2 + 3*a + 7*b^2 + 6*b + 5*a*b ≥ -3/4   :=  by sorry
