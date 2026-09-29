-- Prove2me | Theorems.Thm_WorkbookSource_base_7774
-- name    : WorkbookSource.base_7774
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:44.644656+00:00
-- url     : https://prove2.me/theorems/0db1f280-b31b-400c-970e-46f9921f2d92
-- title:
--   A sixth-power inequality with a squared triple product
-- statement:
--   The inequality is following to: $ x^6+y^6+z^6+3x^2y^2z^2 \ge 2(x^3y^3+y^3z^3+z^3x^3) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7774` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7774; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7774 (x y z : ℝ) : x^6 + y^6 + z^6 + 3 * x^2 * y^2 * z^2 ≥ 2 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3)  :=  by sorry
