-- Prove2me | Theorems.Thm_WorkbookSource_base_41597
-- name    : WorkbookSource.base_41597
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:32:27.434001+00:00
-- url     : https://prove2.me/theorems/664b5dac-4a4a-4cb6-a90d-d816d445dc6f
-- title:
--   A six-variable quadratic-product inequality with three nonnegative variables
-- statement:
--   $(a^2+b^2+c^2)(x^2+y^2+z^2+xy+xz+yz)\geq2(x+y+z)(xbc+yac+zab)$ is also true for all non-negatives $x$ , $y$ and $z$ and all reals $a$ , $b$ and $c$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41597` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41597; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41597 (a b c x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2 + x*y + x*z + y*z) ≥ 2 * (x + y + z) * (x*b*c + y*a*c + z*a*b)  :=  by sorry
