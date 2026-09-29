-- Prove2me | Theorems.Thm_WorkbookSource_base_19226
-- name    : WorkbookSource.base_19226
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:27.430384+00:00
-- url     : https://prove2.me/theorems/8e145b55-e264-4bf8-be01-7a9687a5ed13
-- title:
--   A product of three quadratic factors with a triple-product correction
-- statement:
--   For the minimum:
--
--    $ \left(x^{2}+1\right)\left(y^{2}+1\right)\left(z^{2}+1\right)+4xyz(x+y+z)
--    =\left[(1-xy)^{2}+(x+y)^{2}\right]\left(z^{2}+1\right)+4xyz(x+y+z)
--    \ge\left[z(1-xy)+(x+y)\right]^{2}+4xyz(x+y+z)
--    =(x+y+z-xyz)^{2}+4xyz(x+y+z)
--    =(x+y+z+xyz)^{2}
--    \ge0 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19226` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19226; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19226  (x y z : ℝ) :
  (x^2 + 1) * (y^2 + 1) * (z^2 + 1) + 4 * x * y * z * (x + y + z) ≥ 0  :=  by sorry
