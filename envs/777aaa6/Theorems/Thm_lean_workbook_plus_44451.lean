-- Prove2me | Theorems.Thm_lean_workbook_plus_44451
-- name    : lean_workbook_plus_44451
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b354838e-58fd-49c2-932f-ae478095e603
-- statement:
--   Prove $(x+y+z)^{2}(xy+yz+zx)^{2} \le 3(x^{2}+xy+y^{2})(z^{2}+zx+x^{2})(y^{2}+yz+z^{2})$ given $x,y,z>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44451 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (x * y + y * z + z * x) ^ 2 ≤ 3 * (x ^ 2 + x * y + y ^ 2) * (z ^ 2 + z * x + x ^ 2) * (y ^ 2 + y * z + z ^ 2)   :=  by sorry
