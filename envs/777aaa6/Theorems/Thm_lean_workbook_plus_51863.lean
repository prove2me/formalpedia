-- Prove2me | Theorems.Thm_lean_workbook_plus_51863
-- name    : lean_workbook_plus_51863
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8fd87edf-0af0-4bd4-a0bd-979ef7f7098e
-- statement:
--   By Cauchy-Schwarz $a\sin x+b\cos x\leq|a\sin x+b\cos x|\leq\sqrt{(\sin^2x+\cos^2x)(a^2+b^2)}=\sqrt{a^2+b^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51863 (a b : ℝ) (x : ℝ) :
  a * Real.sin x + b * Real.cos x ≤ Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
