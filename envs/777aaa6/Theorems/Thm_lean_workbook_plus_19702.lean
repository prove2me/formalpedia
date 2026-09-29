-- Prove2me | Theorems.Thm_lean_workbook_plus_19702
-- name    : lean_workbook_plus_19702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a9a8a123-dce0-4b0a-a11a-9383ffbb27e2
-- statement:
--   $xyz=x^2+y^2+z^2 \ge \frac {(x+y+z)^2} 3,x+y+z \ge 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19702 (x y z : ℝ) : (x + y + z >= 9 ∧ x * y * z = x ^ 2 + y ^ 2 + z ^ 2) → x ^ 2 + y ^ 2 + z ^ 2 >= (x + y + z) ^ 2 / 3   :=  by sorry
