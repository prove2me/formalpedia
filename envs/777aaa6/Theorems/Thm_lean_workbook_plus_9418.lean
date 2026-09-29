-- Prove2me | Theorems.Thm_lean_workbook_plus_9418
-- name    : lean_workbook_plus_9418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bf8cde87-cb2e-4dcc-864c-08cbfe8facbc
-- statement:
--   Prove that $\lim_{x\rightarrow p}f(x)=L\Rightarrow \lim_{x\rightarrow p}|f(x)|=|L|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9418 (f : ℝ → ℝ) (p L : ℝ) : (∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Set.Ioo p δ → |f x - L| < ε) → ∀ ε > 0, ∃ δ > 0, ∀ x, x ∈ Set.Ioo p δ → |f x| - |L| < ε   :=  by sorry
