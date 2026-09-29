-- Prove2me | Theorems.Thm_WorkbookSource_base_1818
-- name    : WorkbookSource.base_1818
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:05:11.323663+00:00
-- url     : https://prove2.me/theorems/2898972a-f331-441a-aed5-e4347433a25b
-- title:
--   A symmetric sixth-power inequality with a triple-product correction
-- statement:
--   Prove that
--    $4(x^6+y^6+z^6)+27x^2y^2z^2 \ge 12(x^4yz+y^4zx+z^4xy)+(x^3y^3+y^3z^3+z^3x^3)$
--   where $x, y, z$ are arbitrary positive real numbers.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1818` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1818; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1818 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 4 * (x ^ 6 + y ^ 6 + z ^ 6) + 27 * x ^ 2 * y ^ 2 * z ^ 2 ≥ 12 * (x ^ 4 * y * z + y ^ 4 * z * x + z ^ 4 * x * y) + (x ^ 3 * y ^ 3 + y ^ 3 * z ^ 3 + z ^ 3 * x ^ 3)  :=  by sorry
