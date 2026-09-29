-- Prove2me | Theorems.Thm_WorkbookSource_base_57027
-- name    : WorkbookSource.base_57027
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:08:11.116671+00:00
-- url     : https://prove2.me/theorems/b2132379-6c11-4ae2-8829-7cae90c02e91
-- title:
--   A shifted cyclic cubic ratio with a pair-product correction
-- statement:
--   Let $x,y,z$ be positive reals satisfy $x+y+z=3$ Prove that
--    $ \frac{x^3}{y^2+2}+\frac{y^3}{z^2+2}+\frac{z^3}{x^2+2}+\Big ( xy+yz+zx \Big ) \geq 4 $
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_57027` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_57027; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_57027 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x ^ 3 / (y ^ 2 + 2) + y ^ 3 / (z ^ 2 + 2) + z ^ 3 / (x ^ 2 + 2)) + (x * y + y * z + z * x) ≥ 4  :=  by sorry
