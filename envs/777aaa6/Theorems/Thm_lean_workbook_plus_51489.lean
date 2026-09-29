-- Prove2me | Theorems.Thm_lean_workbook_plus_51489
-- name    : lean_workbook_plus_51489
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/edabfb75-5508-4ad6-a5fe-a27f3852ca46
-- statement:
--   Prove $f(a):=1-\frac 1a-\ln a<0$ for $a>1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51489 (a : ℝ) (ha : 1 < a) : 1 - (1 / a) - Real.log a < 0   :=  by sorry
