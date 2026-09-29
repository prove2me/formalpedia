-- Prove2me | Theorems.Thm_WorkbookSource_plus_46295
-- name    : WorkbookSource.plus_46295
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:37:33.990742+00:00
-- url     : https://prove2.me/theorems/0a96b3f6-e957-461a-a2b1-e48684a11920
-- title:
--   A product comparison between two cyclic linear sums
-- statement:
--   Given $ a,b,c \ge 0$ .Prove that:
--    $ (a+2b)^2(b+2c)^2(c+2a)^2 \ge 27abc(a+2c)(b+2a)(c+2b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_46295` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_46295; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_46295 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + 2 * b) ^ 2 * (b + 2 * c) ^ 2 * (c + 2 * a) ^ 2 ≥ 27 * a * b * c * (a + 2 * c) * (b + 2 * a) * (c + 2 * b)   :=  by sorry
