-- Prove2me | Theorems.Thm_lean_workbook_plus_23853
-- name    : lean_workbook_plus_23853
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/862f258f-f506-4dae-b086-36b37048c983
-- statement:
--   Prove using epsilon delta definition for limits at infinity that \nlim as x tends to infinity of c = c \nand \nlim as x tend to infinity of 1/(x^p) = 0 for p > 0\nYou should take an $\epsilon>0$ and then show that there is a $N \in \mathbb{N}$ such that for all $x > N \in \mathbb{R}$ , we have $|f(x) -l| < \epsilon$ , where $l$ is the desired limit.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23853 (c : ℝ) : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ x : ℝ, x > N → |c - c| < ε   :=  by sorry
