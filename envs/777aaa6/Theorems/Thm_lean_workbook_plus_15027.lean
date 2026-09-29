-- Prove2me | Theorems.Thm_lean_workbook_plus_15027
-- name    : lean_workbook_plus_15027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/64fbe72e-4c16-4d32-ac0e-70687fde53a5
-- statement:
--   If $ab=1$ and $ac+bd=2$ , then prove that $cd{\leq}1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15027 (a b c d : ℝ) (hab : a * b = 1) (h : a * c + b * d = 2) :
  c * d ≤ 1   :=  by sorry
