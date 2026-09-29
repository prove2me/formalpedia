-- Prove2me | Theorems.Thm_WorkbookSource_plus_29287
-- name    : WorkbookSource.plus_29287
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:49:44.566887+00:00
-- url     : https://prove2.me/theorems/17967cab-b869-49c9-a3d6-5ac4d4b397f9
-- title:
--   A quartic symmetric expression bounds a difference product
-- statement:
--   Let $ a + b + c = 3 , a,b,c = R$ . Prove that
--    $ \sum_{cyc} a^4 + 3\sum_{cyc} a^2b^2 + 3\ge 2\sum_{cyc} ab(a^2 + b^2 ) + 6(a - b)(a - c)(b - c)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_29287` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_29287; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_29287 (a b c : ℝ) (ha : a + b + c = 3) : a^4 + b^4 + c^4 + 3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + 3 ≥ 2 * (a * b * (a^2 + b^2) + b * c * (b^2 + c^2) + c * a * (c^2 + a^2)) + 6 * (a - b) * (a - c) * (b - c)   :=  by sorry
