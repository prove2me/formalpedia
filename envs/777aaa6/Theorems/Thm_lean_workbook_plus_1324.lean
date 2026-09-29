-- Prove2me | Theorems.Thm_lean_workbook_plus_1324
-- name    : lean_workbook_plus_1324
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/fc04ec2e-4881-4823-ad4b-8ef3e19f68d7
-- statement:
--   Let \( \epsilon >0 \) be arbitrary. Choose \( N > 1+\log(\frac{1}{\epsilon}) \) so that \( |a_n-\sqrt{2}| \leq \epsilon \) \( \forall n \geq N \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1324 (ε : ℝ) (a : ℕ → ℝ) (N : ℕ) (hN : N > 1 + Real.log (1/ε)) (ha : ∀ n ≥ N, |a n - Real.sqrt 2| ≤ ε) : ∀ n ≥ N, |a n - Real.sqrt 2| ≤ ε   :=  by sorry
