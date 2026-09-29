-- Prove2me | Theorems.Thm_lean_workbook_plus_41094
-- name    : lean_workbook_plus_41094
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/87e7fd05-6631-48d0-8b64-96b6e3b824fe
-- statement:
--   $ \sqrt{\frac{x^2+y^2}{2}}\ge\frac{x+y}{2}$ ; $ \sqrt{\frac{y^2+z^2}{2}}\ge\frac{y+z}{2}$ , $ \sqrt{\frac{z^2+x^2}{2}}\ge\frac{z+x}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41094 (x y z : ℝ) : (Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≥ (x + y) / 2 ∧ Real.sqrt ((y ^ 2 + z ^ 2) / 2) ≥ (y + z) / 2 ∧ Real.sqrt ((z ^ 2 + x ^ 2) / 2) ≥ (z + x) / 2)   :=  by sorry
