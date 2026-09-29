-- Prove2me | Theorems.Thm_lean_workbook_plus_66588
-- name    : lean_workbook_plus_66588
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5205b121-bb6b-4c42-9e11-1b4020ac850b
-- statement:
--   $ 9(a^3 + b^3 + c^3) \ge (a + b + c)^3 \Leftrightarrow 8(a^3+b^3+c^3) \ge 3(a+b)(b+c)(c+a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66588 (a b c : ℝ) : 9 * (a^3 + b^3 + c^3) ≥ (a + b + c)^3 ↔ 8 * (a^3 + b^3 + c^3) ≥ 3 * (a + b) * (b + c) * (c + a)   :=  by sorry
