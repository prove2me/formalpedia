-- Prove2me | Theorems.Thm_lean_workbook_plus_30778
-- name    : lean_workbook_plus_30778
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/7929d419-2471-4802-a964-3584e894c651
-- statement:
--   Does the series $S=1/2+1/4+1/6+1/8+………+1/2n$ have a closed-form expression with standard functions?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30778 : ∃ f : ℕ → ℝ, ∀ n : ℕ, ∑ k in Finset.range n, (1 : ℝ) / (2 * k) = f n   :=  by sorry
