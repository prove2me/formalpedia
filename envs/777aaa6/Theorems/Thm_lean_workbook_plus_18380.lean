-- Prove2me | Theorems.Thm_lean_workbook_plus_18380
-- name    : lean_workbook_plus_18380
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f634a1cb-446e-4e53-ba41-35236b0bb682
-- statement:
--   the maximum value of $a\sin(x) + b\cos(x)$ is $1$ when $a^2 + b^2 = 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18380 (a b : ℝ) (x : ℝ) (h : a^2 + b^2 = 1) :
  a * Real.sin x + b * Real.cos x ≤ 1   :=  by sorry
