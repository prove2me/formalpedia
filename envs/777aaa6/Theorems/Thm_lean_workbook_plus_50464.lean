-- Prove2me | Theorems.Thm_lean_workbook_plus_50464
-- name    : lean_workbook_plus_50464
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b1b1e0e2-701a-4092-a59c-7d472f23d764
-- statement:
--   Let $\log_23 =x, 1<x<2$ (can easy be proved, that $\frac{3}{2}<x<\frac{8}{5})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50464 : 1 < Real.log 3 / Real.log 2 ∧ Real.log 3 / Real.log 2 < 2   :=  by sorry
