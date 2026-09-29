-- Prove2me | Theorems.Thm_lean_workbook_plus_50860
-- name    : lean_workbook_plus_50860
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ae08a050-b812-4c10-bd5c-e545ecb1ceb0
-- statement:
--   either $\cos x=\frac{\pi}2+\sin x+2k\pi$ $\iff$ $\cos(x+\frac{\pi}4)=\frac{(4k+1)\pi}{2\sqrt 2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50860 (x : ℝ) (k : ℤ) : (Real.cos x = Real.pi / 2 + Real.sin x + 2 * Real.pi * k) ↔ (Real.cos (x + Real.pi / 4) = (2 * Real.sqrt 2)⁻¹ * (4 * k + 1) * Real.pi)   :=  by sorry
