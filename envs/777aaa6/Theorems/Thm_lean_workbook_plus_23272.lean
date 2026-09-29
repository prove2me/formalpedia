-- Prove2me | Theorems.Thm_lean_workbook_plus_23272
-- name    : lean_workbook_plus_23272
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d633bdc2-fec2-4f67-b1db-26dd7be917ca
-- statement:
--   Let $ n \geq 2$ be a positive integer. Prove that $ \prod_{k=2}^{n} {(1-\frac {1}{k^3})} > \frac{1}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23272 (n : ℕ) (hn : 2 ≤ n) : (∏ k in Finset.Icc 2 n, (1 - 1 / k ^ 3)) > 1 / 2   :=  by sorry
