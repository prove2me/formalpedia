-- Prove2me | Theorems.Thm_lean_workbook_plus_60260
-- name    : lean_workbook_plus_60260
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a4e8f2f5-1b55-4e9a-84db-268453feadf4
-- statement:
--   Prove that: $a+b=2$ and $a^{4}+b^{4}\geq \frac{(a+b)(a^{3}+b^{3})}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60260 (a b : ℝ) (hab : a + b = 2) : a ^ 4 + b ^ 4 ≥ (a + b) * (a ^ 3 + b ^ 3) / 2   :=  by sorry
