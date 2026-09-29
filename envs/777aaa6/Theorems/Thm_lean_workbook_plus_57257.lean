-- Prove2me | Theorems.Thm_lean_workbook_plus_57257
-- name    : lean_workbook_plus_57257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8ed90b87-3ba5-412f-8ae9-63afc68810ee
-- statement:
--   Suppose $a,b,c$ are reals then show that $\left|a\right|+\left|b\right|+\left|c\right|+\left|a+b+c\right|\ge \left|a+b\right|+\left|b+c\right|+\left|c+a\right|$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57257 (a b c : ℝ) : |a| + |b| + |c| + |a + b + c| ≥ |a + b| + |b + c| + |c + a|   :=  by sorry
