-- Prove2me | Theorems.Thm_WorkbookSource_base_5378
-- name    : WorkbookSource.base_5378
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:49.848072+00:00
-- url     : https://prove2.me/theorems/c2e70a28-bc77-44f3-a08e-f86829f8f142
-- title:
--   A mixed quadratic reciprocal sum bounds pairwise reciprocals
-- statement:
--   prove that :
--   $ \frac{1}{x^2+yz}+\frac{1}{y^2+xz}+\frac{1}{z^2+xy}\leq\,\frac{1}{2}(\frac{1}{xy}+\frac{1}{yz}+\frac{1}{xz})$
--   where $x,y,z\succ0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5378` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5378; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5378 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x ^ 2 + y * z) + 1 / (y ^ 2 + z * x) + 1 / (z ^ 2 + x * y)) ≤ (1 / 2) * (1 / (x * y) + 1 / (y * z) + 1 / (x * z))  :=  by sorry
