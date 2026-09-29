-- Prove2me | Theorems.Thm_lean_workbook_plus_53501
-- name    : lean_workbook_plus_53501
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/bcd16b37-8a16-4789-9473-732b2fe0ea96
-- statement:
--   Demostrar que $\frac{(a+b+c)^2} {3}\geq ab+ac+bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53501 (a b c : ℝ) : (a + b + c) ^ 2 / 3 ≥ a * b + a * c + b * c   :=  by sorry
