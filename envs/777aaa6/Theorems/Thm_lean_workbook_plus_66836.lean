-- Prove2me | Theorems.Thm_lean_workbook_plus_66836
-- name    : lean_workbook_plus_66836
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a4f9438e-8431-434b-b769-4c4bfee123d8
-- statement:
--   Given that $ a_1=1$ , $ a_2=5$ , $ \displaystyle a_{n+1} = \frac{a_n \cdot a_{n-1}}{\sqrt{a_n^2 + a_{n-1}^2 + 1}}$ . Find a expression of the general term of $ \{ a_n \}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66836 (a : ℕ → ℝ) (a1 : a 0 = 1) (a2 : a 1 = 5) (a_rec : ∀ n, a (n + 1) = a n * a (n - 1) / Real.sqrt (a n ^ 2 + a (n - 1) ^ 2 + 1)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n   :=  by sorry
