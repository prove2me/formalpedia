-- Prove2me | Theorems.Thm_lean_workbook_plus_18395
-- name    : lean_workbook_plus_18395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5642b419-52c5-4c7a-8256-422bb0ea2eb1
-- statement:
--   Formula for infinite geometric series with $\abs{r} < 1$ is $\frac{t_1}{1-r}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18395 (t₁ : ℝ) (r : ℝ) (h : 0 < r) (h' : r < 1) : ∑' i : ℕ, t₁ * r ^ i = t₁ / (1 - r)   :=  by sorry
