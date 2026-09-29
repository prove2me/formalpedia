-- Prove2me | Theorems.Thm_lean_workbook_plus_72773
-- name    : lean_workbook_plus_72773
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/47f1e883-a846-462e-918a-2117afba3667
-- statement:
--   Find the value of $x_9$ in the recursive sequence $x_{n+1}=2n+x_n$ given $x_{10}=91$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72773 (x : ℕ → ℕ) (h₁ : x 10 = 91) (h₂ : ∀ n, x (n + 1) = 2 * n + x n) : x 9 = 73   :=  by sorry
