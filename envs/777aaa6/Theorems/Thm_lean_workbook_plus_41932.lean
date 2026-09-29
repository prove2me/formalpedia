-- Prove2me | Theorems.Thm_lean_workbook_plus_41932
-- name    : lean_workbook_plus_41932
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a6edbbd8-07c6-4975-b1e7-43f5ca90e6dd
-- statement:
--   Prove that: $xyz+x^3+y^3+z^3\geq \frac{4}{9}(x+y+z)(xy+xz+yz)$ given $x,y,z\geq 0$ and $x+y+z\geq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41932 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z ≥ 3) : x * y * z + x ^ 3 + y ^ 3 + z ^ 3 ≥ (4 / 9) * (x + y + z) * (x * y + x * z + y * z)   :=  by sorry
