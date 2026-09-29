-- Prove2me | Theorems.Thm_lean_workbook_plus_3775
-- name    : lean_workbook_plus_3775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a228691f-bffe-4e6d-8fa7-3aca3aee305a
-- statement:
--   Without loss of generality, let $a_1\ge a_2 \ge ... \ge a_n$ . \n\nThen clearly, $a_1-1\ge a_2-1\ge ... \ge a_n-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3775  (n : ℕ)
  (a : ℕ → ℕ)
  (h₀ : 0 < n)
  (h₁ : ∀ i, 0 < i → a i ≥ a (i + 1)) :
  ∀ i, 0 < i → a i - 1 ≥ a (i + 1) - 1   :=  by sorry
