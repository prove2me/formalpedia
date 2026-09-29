-- Prove2me | Theorems.Thm_lean_workbook_plus_62853
-- name    : lean_workbook_plus_62853
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/59b54b26-2384-4d80-bcde-4d8b85e4b147
-- statement:
--   Given eight real numbers $a,b,c,d,e,f,g,h$ . Prove that at least one of the six numbers $ac+bd,ae+bf,ag+bh,ce+df,cg+dh,eg+fh$ is nonnegative.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62853 (a b c d e f g h : ℝ) :
  ac + bd ≥ 0 ∨ ae + bf ≥ 0 ∨ ag + bh ≥ 0 ∨
  ce + df ≥ 0 ∨ cg + dh ≥ 0 ∨ eg + fh ≥ 0   :=  by sorry
