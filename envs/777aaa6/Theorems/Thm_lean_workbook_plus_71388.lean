-- Prove2me | Theorems.Thm_lean_workbook_plus_71388
-- name    : lean_workbook_plus_71388
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fca0b1e9-70d6-4e05-beb3-4387f1b0a968
-- statement:
--   Since $-1\leq f(x)\leq 1$, then $f(x+am)-f(x)$ is bounded.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71388 (f : ℝ → ℝ) (m : ℝ) (hf: ∀ x, -1 ≤ f x ∧ f x ≤ 1) : ∃ M, ∀ x, |f (x + m) - f x| ≤ M   :=  by sorry
