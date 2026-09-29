-- Prove2me | Theorems.Thm_lean_workbook_plus_13915
-- name    : lean_workbook_plus_13915
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/20fc6332-531f-44b4-b45e-2c87257e87de
-- statement:
--   Show that the series $(b_{n})_{n\in\mathbb{N}}$ with $b_{n}=1+\dfrac{1}{2}+\dfrac{1}{3}+...+\dfrac{1}{n}-\ln({n+\dfrac{1}{2}})$ is strictly decreasing.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13915 : ∀ n : ℕ, (1 + ∑ k in Finset.range n, (1 : ℝ) / (k + 1)) - Real.log (n + 1 / 2) < (1 + ∑ k in Finset.range (n + 1), (1 : ℝ) / (k + 1)) - Real.log (n + 1 / 2)   :=  by sorry
