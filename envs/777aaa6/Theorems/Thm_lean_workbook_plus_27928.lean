-- Prove2me | Theorems.Thm_lean_workbook_plus_27928
-- name    : lean_workbook_plus_27928
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/57bde65e-3fc9-4bfb-a467-63679fb32237
-- statement:
--   Now, $x^2+y^2+z^2\geqslant 3\left(\dfrac{x+y+z}{3}\right)^2=3\left(\dfrac{1}{3}\right)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27928 (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 3 * (x + y + z) ^ 2 / 9   :=  by sorry
