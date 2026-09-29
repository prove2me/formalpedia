-- Prove2me | Theorems.Thm_lean_workbook_plus_28012
-- name    : lean_workbook_plus_28012
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ed090443-5e2e-4a91-bd2b-e992cbc9e176
-- statement:
--   $(f(x)-f(\frac 1x))^2=0$ and so $f(\frac 1x)=f(x)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28012 (f : ℝ → ℝ) (hf: (f x - f (1/x))^2 = 0) : f (1/x) = f x   :=  by sorry
