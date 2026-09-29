-- Prove2me | Theorems.Thm_lean_workbook_plus_62589
-- name    : lean_workbook_plus_62589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/edb52116-5402-4bcf-90c9-6c07033e2db7
-- statement:
--   Let $a,b\geq 0 $ and $ a+b=3.$ Prove that $$27\geq a^3+b^3+3ab\geq \frac{27}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62589 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 3) : 27 ≥ a^3 + b^3 + 3 * a * b ∧ a^3 + b^3 + 3 * a * b ≥ 27 / 2   :=  by sorry
