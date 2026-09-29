-- Prove2me | Theorems.Thm_lean_workbook_plus_250
-- name    : lean_workbook_plus_250
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a9dd773e-1581-4ecc-b17d-80f77f016f2f
-- statement:
--   For any $k\in \mathbb{R}$, show that $f(x)=kx$ is a solution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_250 (k : ℝ) (f : ℝ → ℝ) (hf: f = fun x ↦ k * x) : f x = k * x   :=  by sorry
