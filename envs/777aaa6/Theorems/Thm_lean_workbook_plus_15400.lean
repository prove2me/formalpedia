-- Prove2me | Theorems.Thm_lean_workbook_plus_15400
-- name    : lean_workbook_plus_15400
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1c933804-b762-43d6-ad02-fc152d2038c2
-- statement:
--   Prove that if the product of $ n$ numbers is equal to $ n$ and the sum of these numbers is equal to $ 0$, then $ n$ is divisible by $ 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15400 (n : ℕ) (a : ℕ → ℕ) (h₁ : ∏ i in Finset.range n, a i = n) (h₂ : ∑ i in Finset.range n, a i = 0) : 4 ∣ n   :=  by sorry
