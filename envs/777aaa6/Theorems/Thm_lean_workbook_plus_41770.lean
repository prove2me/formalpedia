-- Prove2me | Theorems.Thm_lean_workbook_plus_41770
-- name    : lean_workbook_plus_41770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/449d35f8-86e6-4b4d-a235-5a2864170698
-- statement:
--   Prove that for $x, y, z \geq 0$, the following inequality holds: $x^3 + y^3 + z^3 + x^2y + y^2z + z^2x \geq 2(xy^2 + yz^2 + zx^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41770 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : x ^ 3 + y ^ 3 + z ^ 3 + x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≥ 2 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2)   :=  by sorry
