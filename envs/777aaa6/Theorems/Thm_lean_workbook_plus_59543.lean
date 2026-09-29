-- Prove2me | Theorems.Thm_lean_workbook_plus_59543
-- name    : lean_workbook_plus_59543
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/b9c30a27-586d-4af3-89ca-01d1b97c54ff
-- statement:
--   Let $a,b >0 $ and $ \dfrac{2}{1+a}+\dfrac{5}{1+b} \le 1.$ Prove that \n $$5a+2b\geq 33$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59543 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (2 / (1 + a) + 5 / (1 + b) ≤ 1 → 5 * a + 2 * b ≥ 33)   :=  by sorry
