-- Prove2me | Theorems.Thm_lean_workbook_plus_74967
-- name    : lean_workbook_plus_74967
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/399fc847-424d-4567-bde7-f16c984d4b2f
-- statement:
--   Expected value = $\frac{1}{50} \cdot 1 + \frac{1}{50} \cdot 1+ \cdots + \frac{1}{50} \cdot 1$ (75 times) Expected value = $\frac{1}{50} \cdot 75 = \boxed{\frac{3}{2}}$ nuggets.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74967  (v : ℕ → ℝ)
  (h₀ : ∀ n, v n = 1 / 50) :
  ∑ k in Finset.range 75, v k = 3 / 2   :=  by sorry
