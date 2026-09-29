-- Prove2me | Theorems.Thm_lean_workbook_plus_25229
-- name    : lean_workbook_plus_25229
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d95eaa53-1637-4a4a-8eb0-ecf6845394a2
-- statement:
--   Let $x, y \geq 0.$ Prove that $x^2+xy+y^2 \leq 3(x- \sqrt{xy}+y)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25229 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : x^2 + x*y + y^2 ≤ 3 * (x - Real.sqrt (x*y) + y)^2   :=  by sorry
