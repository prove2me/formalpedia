-- Prove2me | Theorems.Thm_lean_workbook_plus_2795
-- name    : lean_workbook_plus_2795
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/805850d4-e653-4817-b6a8-1013248f2c01
-- statement:
--   Apply the C.B.S. - inequality $:\ |ax+by+cz|^2\le \left(a^2+b^2+c^2\right)\left(x^2+y^2+z^2\right)$ . You have the equality if and only if $\frac xa=\frac yb=\frac zc$ . See about the C.B.S. - inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2795 (a b c x y z : ℝ) : (a * x + b * y + c * z) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2)   :=  by sorry
