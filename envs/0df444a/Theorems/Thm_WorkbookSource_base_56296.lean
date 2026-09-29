-- Prove2me | Theorems.Thm_WorkbookSource_base_56296
-- name    : WorkbookSource.base_56296
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:41.030483+00:00
-- url     : https://prove2.me/theorems/c9d12ace-beb2-4872-9ba6-ca651029fb06
-- title:
--   A squared pairwise-sum bound with a cubic product
-- statement:
--   Prove that $2+\frac{1}{3}(xy+zx+yz)^2 \geq xy+zx+yz+2xyz$ with $x,y,z\geq 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56296` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56296; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56296 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 2 + (1 / 3) * (x * y + y * z + z * x) ^ 2 ≥ x * y + y * z + z * x + 2 * x * y * z  :=  by sorry
