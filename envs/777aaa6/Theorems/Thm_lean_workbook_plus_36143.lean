-- Prove2me | Theorems.Thm_lean_workbook_plus_36143
-- name    : lean_workbook_plus_36143
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/940879bb-cdcb-44e1-bdbe-818401839e7d
-- statement:
--   $ a\log_e (x) = \log_e (x^a) \qquad(1)$\n\n $ \log_e (x) + \log_e (y) = \log_e (xy) \qquad(2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36143 (a x : ℝ) (h₁ : x > 0) : a * Real.log x = Real.log (x ^ a)   :=  by sorry
