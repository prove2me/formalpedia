-- Prove2me | Theorems.Thm_lean_workbook_plus_78758
-- name    : lean_workbook_plus_78758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/98bf94b3-a1bf-4976-980b-9f7d0bb8f2a4
-- statement:
--   For which non-negative integers $n$ does there exist a non-periodic function $f : R \rightarrow R$ such that $f(x+1)+f(x-1)=\sqrt{n} f(x)$ for all $x \in R$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78758 (n : ℕ) (hn : 0 < n) : ∃ f : ℝ → ℝ, ¬ ∃ T > 0, ∀ x, f (x + T) = f x ∧ ∀ x, f (x + 1) + f (x - 1) = Real.sqrt n * f x   :=  by sorry
