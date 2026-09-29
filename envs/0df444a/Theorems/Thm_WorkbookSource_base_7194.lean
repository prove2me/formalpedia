-- Prove2me | Theorems.Thm_WorkbookSource_base_7194
-- name    : WorkbookSource.base_7194
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:38.292173+00:00
-- url     : https://prove2.me/theorems/ffbc6f04-88ad-48d8-a6b3-96d0551e37ec
-- title:
--   A cyclic quartic expression bounds a fourth power of the sum
-- statement:
--   Prove that $x(x+y)^3+y(y+z)^3+z(z+x)^3 \ge \frac{8}{27} (x+y+z)^4$ for real numbers $x, y, z$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7194` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7194; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7194 (x y z : ℝ) : x * (x + y) ^ 3 + y * (y + z) ^ 3 + z * (z + x) ^ 3 ≥ (8 / 27) * (x + y + z) ^ 4  :=  by sorry
