-- Prove2me | Theorems.Thm_lean_workbook_plus_43796
-- name    : lean_workbook_plus_43796
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/4f148a43-4408-43f4-b5b7-b5bc776e2a12
-- statement:
--   Let $ P(n)$ the sum of the digits of the number pairs n. For example, $ P(1234) = 2 +4 = 6$ . What is the value of $ P(1) + P(2) + P(3) + ... + P(100)$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43796 (P : ℕ → ℕ) (hP : ∀ n, P n = (Nat.digits 10 n).sum) : ∑ i in Finset.range 101, P i = 400   :=  by sorry
