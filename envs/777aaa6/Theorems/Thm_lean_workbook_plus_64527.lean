-- Prove2me | Theorems.Thm_lean_workbook_plus_64527
-- name    : lean_workbook_plus_64527
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/fa788bd9-9014-4ac9-b87b-7f762082dffc
-- statement:
--   From AM-GM, we get that $\frac{x^2y^2+y^2z^2}{2} \geq xy^2z$ $\frac{y^2z^2+z^2x^2}{2} \geq xyz^2$ $\frac{x^2y^2+z^2x^2}{2} \geq x^2yz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64527 (x y z : ℝ) :
  (x^2 * y^2 + y^2 * z^2) / 2 ≥ x * y^2 * z ∧
  (y^2 * z^2 + z^2 * x^2) / 2 ≥ x * y * z^2 ∧
  (x^2 * y^2 + z^2 * x^2) / 2 ≥ x^2 * y * z   :=  by sorry
