-- Prove2me | Theorems.Thm_lean_workbook_plus_61583
-- name    : lean_workbook_plus_61583
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/3ee3fb69-8159-4a42-8ae2-019c1962c468
-- statement:
--   Consecutive terms summed look like this $2^k\frac{2}{k+2} +2^{k+1}\frac{2}{k+3}-2^k\frac{1}{k+1}-2^{k+1}\frac{1}{k+2}=\frac{2^{k+2}}{k+3}-\frac{2^k}{k+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61583 : ∀ k : ℕ, (2:ℝ)^k * (2/(k+2)) + (2:ℝ)^(k+1) * (2/(k+3)) - (2:ℝ)^k * (1/(k+1)) - (2:ℝ)^(k+1) * (1/(k+2)) = (2:ℝ)^(k+2) / (k+3) - (2:ℝ)^k / (k+1)   :=  by sorry
