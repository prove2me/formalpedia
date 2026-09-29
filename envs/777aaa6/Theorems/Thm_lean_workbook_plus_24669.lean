-- Prove2me | Theorems.Thm_lean_workbook_plus_24669
-- name    : lean_workbook_plus_24669
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/549385fb-08ac-40d3-9346-b6cf68fc796b
-- statement:
--   Prove that $0 \le \ln(1+t) \le t$ for $t \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24669 (t : ℝ) (ht : 0 ≤ t) : 0 ≤ Real.log (1 + t) ∧ Real.log (1 + t) ≤ t   :=  by sorry
