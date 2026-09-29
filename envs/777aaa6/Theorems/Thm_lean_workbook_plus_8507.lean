-- Prove2me | Theorems.Thm_lean_workbook_plus_8507
-- name    : lean_workbook_plus_8507
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f9dd1b58-8ecc-4f24-8b5b-533b8b34e1fe
-- statement:
--   Using the identity $ \frac{1}{k(k+1)(k+2)} = \frac{1}{2}\left( \frac{1}{k(k+1)} -\frac{1}{(k+1)(k+2)} \right )$ we telescope the sum as \n\n $ \frac{1}{1\cdot 2\cdot 3}+\frac{1}{2\cdot 3\cdot 4}+\frac{1}{3\cdot 4\cdot 5}+...+\frac{1}{n\cdot (n+1)\cdot (n+2)} = \frac{1}{2} \left ( \frac{1}{2} - \frac{1}{(n+1)(n+2)}\right)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8507 : ∀ n : ℕ, ∑ k in Finset.range (n+1), (1 : ℝ) / (k * (k + 1) * (k + 2)) = 1 / 2 * (1 / 2 - 1 / (n + 1) / (n + 2))   :=  by sorry
