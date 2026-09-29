-- Prove2me | Theorems.Thm_lean_workbook_plus_76558
-- name    : lean_workbook_plus_76558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e282be3e-efae-42a9-bc6b-e06a4e137710
-- statement:
--   prove that $\frac{1}{k^2}\le \frac{1}{k(k-1)}$ for $k \geq2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76558 (k : ℕ) (h₀ : 2 ≤ k) : (1 : ℝ)/(k^2) ≤ 1/(k * (k - 1))   :=  by sorry
