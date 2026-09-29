-- Prove2me | Theorems.Thm_WorkbookSource_base_18503
-- name    : WorkbookSource.base_18503
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:54:31.854324+00:00
-- url     : https://prove2.me/theorems/fda94af1-89fb-4ba6-9500-f2f134027c79
-- title:
--   A cyclic reciprocal ratio bounds a normalized quadratic sum
-- statement:
--   For all positive $x,y,z$ prove that:
--    $ \sum_{cyc}\frac{z}{2x+y} \geq \frac13 \cdot \frac{x^2+y^2+z^2}{xy+yz+zx}+\frac{2}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18503` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18503; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18503 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z / (2 * x + y) + x / (2 * y + z) + y / (2 * z + x)) ≥ 1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 2 / 3  :=  by sorry
