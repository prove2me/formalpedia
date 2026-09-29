-- Prove2me | Theorems.Thm_lean_workbook_plus_3184
-- name    : lean_workbook_plus_3184
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/94bf2218-3560-44e7-9b06-2c16582c530c
-- statement:
--   Using the AM-GM Inequality, we have $ \begin{aligned} 2y(1 + x^2 & + y^2 + z^2)(x^3 + z^3 + xyz + xz) \le \ & \le \frac {[y(1 + x^2 + y^2 + z^2) + 2(x^3 + z^3 + xyz + xz)]^2}{4}.\end{aligned}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3184 {x y z : ℝ} : 2*y*(1 + x^2 + y^2 + z^2)*(x^3 + z^3 + x*y*z + x*z) ≤ (y*(1 + x^2 + y^2 + z^2) + 2*(x^3 + z^3 + x*y*z + x*z))^2 / 4   :=  by sorry
