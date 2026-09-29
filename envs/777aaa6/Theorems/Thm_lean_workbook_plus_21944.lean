-- Prove2me | Theorems.Thm_lean_workbook_plus_21944
-- name    : lean_workbook_plus_21944
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/59e79931-de1e-44d3-9e4f-5d6f3a9b5b42
-- statement:
--   Discuss the convergence of the series $A = \sum_{n\ge 1}\frac{a^n}{n!}$ for any real number $a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21944 : ∀ a : ℝ, ∃ l : ℝ, ∑' n : ℕ, (a ^ n / n.factorial) = l   :=  by sorry
