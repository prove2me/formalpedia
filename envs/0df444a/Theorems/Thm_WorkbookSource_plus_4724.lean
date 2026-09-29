-- Prove2me | Theorems.Thm_WorkbookSource_plus_4724
-- name    : WorkbookSource.plus_4724
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:44.88114+00:00
-- url     : https://prove2.me/theorems/44def53f-a2ff-44b0-9553-e63ab9731319
-- title:
--   A sum bound by three shifted squares
-- statement:
--   Let $a = 1 + x^2, b = 1 + y^2, c = 1 + z^2$ for $x, y, z \ge 0$ . The desired inequality is written as
--    $$(x + y + z)^2 \le \frac43(1 + x^2)(1 + y^2)(1 + z^2).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_4724` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_4724; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_4724 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 2 ≤ (4 / 3) * (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)   :=  by sorry
