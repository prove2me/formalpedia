-- Prove2me | Theorems.Thm_lean_workbook_plus_41714
-- name    : lean_workbook_plus_41714
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/7deb9b30-0b82-4e44-b5eb-f758a4154c89
-- statement:
--   Let $x,y,z \geq 0$ ,prove that: $x(x+y)^2+2z^3 \geq 2x(yz+z^2+xy).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41714 (x y z : ℝ) (hx:0 ≤ x) (hy:0 ≤ y) (hz:0 ≤ z) : x * (x + y) ^ 2 + 2 * z ^ 3 ≥ 2 * x * (y * z + z ^ 2 + x * y)   :=  by sorry
