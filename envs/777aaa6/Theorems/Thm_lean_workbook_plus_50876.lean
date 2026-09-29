-- Prove2me | Theorems.Thm_lean_workbook_plus_50876
-- name    : lean_workbook_plus_50876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/dbc49ff4-8329-484b-8e76-f781cebae22e
-- statement:
--   From the first condition and the symmetry that it creates, we know that the probability of getting heads on the first coin is the same as the probability of getting tails on the second coin. Let this probability be $p$ . Also, the probability of getting tails on the first coin is the same as the probability of getting heads on the second coin. Let this probability be $(1-p)$ .\n\nFrom the second condition, we know that $p^2 + (1-p)^2 = \frac{5}{8}$ . This leads to $16p^2 - 16p +3 =0$ , which leads to $p = \frac{1}{4}, \frac{3}{4}$ . Since we don't really know which coin is which, this actually makes perfect sense...especially the fact that the probabilities sum to $1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50876  (p : ℝ)
  (h₀ : 0 ≤ p ∧ p ≤ 1)
  (h₁ : (p^2) + ((1 - p)^2) = 5 / 8) :
  p = 1 / 4 ∨ p = 3 / 4   :=  by sorry
