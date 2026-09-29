-- Prove2me | Theorems.Thm_lean_workbook_plus_24542
-- name    : lean_workbook_plus_24542
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6b46de27-4a48-4470-90d2-2a225a557f2c
-- statement:
--   Prove that, \n $ \frac{1}{2}.\frac{3}{4}.\frac{5}{6}....\frac{2n-1}{2n}\leq{\frac{1}{\sqrt{3n+1}}},$ $ n\geq{1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24542 : ∀ n : ℕ, n >= 1 → (∏ k in Finset.Icc 1 n, (2 * k - 1) / (2 * k)) ≤ 1 / (Real.sqrt (3 * n + 1))   :=  by sorry
