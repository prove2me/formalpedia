-- Prove2me | Theorems.Thm_lean_workbook_plus_77675
-- name    : lean_workbook_plus_77675
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/e7a2ab8f-4887-4f78-bb6c-cdfd0b2a8515
-- statement:
--   No need to throw complex numbers in here. Just use your stock Pythagorean triples: $(x^2 - y^2)^2 + (2xy)^2 = (x^2 + y^2)^2$ . \n Hence, $25(x^2 + y^2) = (x^2 + y^2)^2$ and so $(x^2 + y^2)(x^2 + y^2 - 25) = 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77675  (x y : ℝ) :
  25 * (x^2 + y^2) = (x^2 + y^2)^2 ↔ (x^2 + y^2) * (x^2 + y^2 - 25) = 0   :=  by sorry
