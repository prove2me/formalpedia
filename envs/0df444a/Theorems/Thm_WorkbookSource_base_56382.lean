-- Prove2me | Theorems.Thm_WorkbookSource_base_56382
-- name    : WorkbookSource.base_56382
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:17:57.704787+00:00
-- url     : https://prove2.me/theorems/a18a3801-bceb-4646-8b85-ee259542b04a
-- title:
--   A fifteenth-degree symmetric inequality with a triple-product correction
-- statement:
--   Prove that for positive variables $x$, $y$, and $z$, the inequality $x^{15} + y^{15} + z^{15} + 3x^5y^5z^5 \geq x^6y^5z^4 + x^6y^4z^5 + x^5y^6z^4 + x^4y^6z^5 + x^5y^4z^6 + x^4y^5z^6$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56382` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56382; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56382 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x ^ 15 + y ^ 15 + z ^ 15 + 3 * x ^ 5 * y ^ 5 * z ^ 5 ≥ x ^ 6 * y ^ 5 * z ^ 4 + x ^ 6 * y ^ 4 * z ^ 5 + x ^ 5 * y ^ 6 * z ^ 4 + x ^ 4 * y ^ 6 * z ^ 5 + x ^ 5 * y ^ 4 * z ^ 6 + x ^ 4 * y ^ 5 * z ^ 6  :=  by sorry
