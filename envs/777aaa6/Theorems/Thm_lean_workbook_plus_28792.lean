-- Prove2me | Theorems.Thm_lean_workbook_plus_28792
-- name    : lean_workbook_plus_28792
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/ec12f9d7-5edd-44f4-85ff-46571e4f4ea6
-- statement:
--   prove that: \n\n $x^2(b+c)^2+y^2(c+a)^2+z^2(a+b)^2 \geq \frac{1}{3}(xy+zx+yz)((b+c)^2+(c+a)^2+(a+b)^2-(c-b)^2-(a-c)^2-(b-a)^2) $ . \n\nBQ \n\n\n（等价于一个加权几何不等式。)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28792 ∀ x y z a b c : ℝ, x^2 * (b + c)^2 + y^2 * (c + a)^2 + z^2 * (a + b)^2 ≥ 1 / 3 * (x * y + y * z + z * x) * ((b + c)^2 + (c + a)^2 + (a + b)^2 - (c - b)^2 - (a - c)^2 - (b - a)^2)   :=  by sorry
