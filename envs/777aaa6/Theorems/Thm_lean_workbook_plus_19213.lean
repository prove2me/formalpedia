-- Prove2me | Theorems.Thm_lean_workbook_plus_19213
-- name    : lean_workbook_plus_19213
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6fc415df-d9f1-4303-be17-abe3a2b6e349
-- statement:
--   Prove that: $\sin(3x)=4\sin(x)\sin\left(\frac{\pi}{3}-x\right)\sin\left(\frac{\pi}{3}+x\right)$ using the complex exponential form $e^{ix}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19213 (x : ℝ) : Real.sin (3*x) = 4*Real.sin x * Real.sin (π/3 - x) * Real.sin (π/3 + x)   :=  by sorry
