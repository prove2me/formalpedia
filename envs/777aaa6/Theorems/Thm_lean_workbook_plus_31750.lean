-- Prove2me | Theorems.Thm_lean_workbook_plus_31750
-- name    : lean_workbook_plus_31750
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b2bc514e-d2e3-480a-881e-09191f811215
-- statement:
--   $(a-1)f(-1)=0$ and so $f(-1)=0$ or $a=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31750 (a : ℝ) (f : ℝ → ℝ) (hf: (a-1)*f (-1) = 0) : f (-1) = 0 ∨ a = 1   :=  by sorry
