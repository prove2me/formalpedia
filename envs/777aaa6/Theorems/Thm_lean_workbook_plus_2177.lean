-- Prove2me | Theorems.Thm_lean_workbook_plus_2177
-- name    : lean_workbook_plus_2177
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/bdf3b758-858a-4680-91a8-d5a23dfd8118
-- statement:
--   Prove that : $\sqrt{(1+a)(1+b)}$ ≥ $1+$ $\sqrt{ab}$ where a,b >0
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2177 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : Real.sqrt ((1 + a) * (1 + b)) ≥ 1 + Real.sqrt (a * b)   :=  by sorry
