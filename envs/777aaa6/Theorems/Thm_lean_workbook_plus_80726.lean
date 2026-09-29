-- Prove2me | Theorems.Thm_lean_workbook_plus_80726
-- name    : lean_workbook_plus_80726
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/054d8613-159f-4c47-9210-bba2bb894bec
-- statement:
--   Let $a=x+y, b=y+z, c=z+x$ (Ravi substitution), we get $x,y,z>0$. After expanding, it suffices to prove: $6(x^3+y^3+z^3)+5(yx^2+zy^2+xz^2)>=11(xy^2+yz^2+zx^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80726 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 6 * (x ^ 3 + y ^ 3 + z ^ 3) + 5 * (y * x ^ 2 + z * y ^ 2 + x * z ^ 2) ≥ 11 * (x * y ^ 2 + y * z ^ 2 + z * x ^ 2)   :=  by sorry
