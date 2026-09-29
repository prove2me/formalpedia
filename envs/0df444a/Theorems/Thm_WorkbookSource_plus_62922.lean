-- Prove2me | Theorems.Thm_WorkbookSource_plus_62922
-- name    : WorkbookSource.plus_62922
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:41.676517+00:00
-- url     : https://prove2.me/theorems/1670a157-f0dc-4b18-a6a4-5c1eb2153d50
-- title:
--   A cyclic sixth-power inequality with mixed terms
-- statement:
--   prove that
--    $ \sum_{cyc}(4x^6 + x^4y^2 + x^4z^2 - 6x^3y^3)\geq0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_62922` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_62922; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_62922 (x y z : ℝ) : (4 * x ^ 6 + x ^ 4 * y ^ 2 + x ^ 4 * z ^ 2 - 6 * x ^ 3 * y ^ 3) + (4 * y ^ 6 + y ^ 4 * z ^ 2 + y ^ 4 * x ^ 2 - 6 * y ^ 3 * z ^ 3) + (4 * z ^ 6 + z ^ 4 * x ^ 2 + z ^ 4 * y ^ 2 - 6 * z ^ 3 * x ^ 3) ≥ 0   :=  by sorry
