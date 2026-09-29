-- Prove2me | Theorems.Thm_lean_workbook_plus_26333
-- name    : lean_workbook_plus_26333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/616af7be-d5bb-4588-a69a-0968f7c51484
-- statement:
--   By AM GM, $(ab+bc+ca)^2\geq3abc(a+b+c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26333 {a b c : ℝ} : (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
