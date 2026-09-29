-- Prove2me | Theorems.Thm_lean_workbook_plus_13077
-- name    : lean_workbook_plus_13077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3ad59ddf-b051-4232-ad58-452cdc8c931e
-- statement:
--   Prove the equality $\sum_{n=0}^{\infty}x^{n}=\frac{1}{1-x}$ for $|x|<1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13077 (x : ℝ) (hx : abs x < 1) : ∑' n : ℕ, x ^ n = 1 / (1 - x)   :=  by sorry
