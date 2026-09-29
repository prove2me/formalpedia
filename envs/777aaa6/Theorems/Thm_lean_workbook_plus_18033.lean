-- Prove2me | Theorems.Thm_lean_workbook_plus_18033
-- name    : lean_workbook_plus_18033
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/af0c19f5-4f6b-4b2c-a436-71fe6535a683
-- statement:
--   Prove that : $ \sum^{n}_{j=0} (2^{j}C^{3n+2-j}_{j}-2^{j-1}C^{3n+1-j}_{j-1})=2^{3n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18033 : ∀ n : ℕ, ∑ j in Finset.range (n + 1), (2^j * Nat.choose (3 * n + 2 - j) j - 2^(j - 1) * Nat.choose (3 * n + 1 - j) (j - 1)) = 2^(3 * n)   :=  by sorry
