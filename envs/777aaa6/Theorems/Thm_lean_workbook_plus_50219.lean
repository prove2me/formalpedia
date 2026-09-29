-- Prove2me | Theorems.Thm_lean_workbook_plus_50219
-- name    : lean_workbook_plus_50219
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/092a7fff-ded2-42d0-bfeb-0b956eb09a4d
-- statement:
--   If $|a-b|<\epsilon\,\forall\,\epsilon>0$, then prove that $a=b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50219  (a b : ℝ)
  (h : ∀ ε > 0, |a - b| < ε) :
  a = b   :=  by sorry
