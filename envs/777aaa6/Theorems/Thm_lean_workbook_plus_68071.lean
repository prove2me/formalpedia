-- Prove2me | Theorems.Thm_lean_workbook_plus_68071
-- name    : lean_workbook_plus_68071
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/7171eb84-d9b2-417f-9612-d5752463677d
-- statement:
--   Since $ a^{2}+1\geq 2a,\ b^{2}+1\geq 2b,\ c^{2}+1\geq 2c$ , we have $ a^{2}+b^{2}+c^{2}+3\geq 2(a+b+c)\ \cdots [1]$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68071 (a b c : ℝ) : a^2 + b^2 + c^2 + 3 ≥ 2 * (a + b + c)   :=  by sorry
