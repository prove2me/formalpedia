-- Prove2me | Theorems.Thm_lean_workbook_plus_18095
-- name    : lean_workbook_plus_18095
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/333685f5-eaed-44cc-9a77-36121176e0ec
-- statement:
--   Prove that for real numbers $x, y, z$,\n$a. (x^2z^2 + x^2y^2 + y^2z^2)^2 \geq 3(x^2 + y^2 + z^2)x^2y^2z^2$\n$b. (x^4 + y^4 + z^4)(x^2z^2 + x^2y^2 + y^2z^2) \geq (xy^3 + yz^3 + x^3z)^2$\n$c. (x^2 + y^2 + z^2)^4 \geq \frac{9}{2}(y^3x + z^3y + x^3z)^2 + \frac{9}{2}(z^3x + x^3y + y^3z)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18095 {x y z : ℝ} : (x^2 * z^2 + x^2 * y^2 + y^2 * z^2)^2 ≥ 3 * (x^2 + y^2 + z^2) * x^2 * y^2 * z^2   :=  by sorry
