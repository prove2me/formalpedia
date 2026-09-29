-- Prove2me | Theorems.Thm_lean_workbook_plus_61894
-- name    : lean_workbook_plus_61894
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/476ac056-3588-408f-a8d6-2dcfc3364287
-- statement:
--   Prove that $ (\frac{1}{2})(\frac{3}{4})\cdots(\frac{2n-1}{2n})\leq\frac{1}{\sqrt{3n}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61894 : ∀ n : ℕ, (∏ k in Finset.range n, ((2 * k - 1) / (2 * k))) ≤ 1 / (Real.sqrt (3 * n))   :=  by sorry
