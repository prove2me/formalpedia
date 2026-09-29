-- Prove2me | Theorems.Thm_lean_workbook_plus_15716
-- name    : lean_workbook_plus_15716
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/a056b4f9-447c-4e12-a0bc-7be78537bf5c
-- statement:
--   Prove that there is no function $f: \mathbb{N} \rightarrow \mathbb{N}$ satisfying $f(n) = f(f(n-1)) + f(f(n+1))$ for all $n > 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15716 : ¬∃ f : ℕ → ℕ, ∀ n > 1, f n = f (f (n - 1)) + f (f (n + 1))   :=  by sorry
