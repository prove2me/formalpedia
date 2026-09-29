-- Prove2me | Theorems.Thm_lean_workbook_plus_73105
-- name    : lean_workbook_plus_73105
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/8cb3f94a-c882-41bf-9de4-8bd2c623f09a
-- statement:
--   Let $a_1, a_2, a_3, a_4, a_5 \in [0, 1]$. Prove that $\prod_{1 \le i < j \le 5} |a_i - a_j| \le \frac{3\sqrt{21}}{38416}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73105 (a : Fin 5 → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 1) :
  ∏ i in Finset.univ, ∏ j in Finset.univ, |a i - a j| ≤ (3 * Real.sqrt 21) / 38416   :=  by sorry
