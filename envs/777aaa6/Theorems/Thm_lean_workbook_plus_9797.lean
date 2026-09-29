-- Prove2me | Theorems.Thm_lean_workbook_plus_9797
-- name    : lean_workbook_plus_9797
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a5abdad5-9dea-4be0-ae3b-2b3dd1758f1b
-- statement:
--   Given $b^2-a^2=c^2-b^2$, prove that $\frac 1{b+c}-\frac 1{a+c}=\frac 1{a+b}-\frac 1{a+c}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9797 :  ∀ a b c : ℝ, b^2 - a^2 = c^2 - b^2 → 1 / (b + c) - 1 / (a + c) = 1 / (a + b) - 1 / (a + c)   :=  by sorry
