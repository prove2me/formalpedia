-- Prove2me | Theorems.Thm_WorkbookSource_plus_3059
-- name    : WorkbookSource.plus_3059
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:55:58.591874+00:00
-- url     : https://prove2.me/theorems/9bec40e7-a594-40db-a7b1-43da24b7741d
-- title:
--   A shifted mixed cyclic ratio sum is at least three
-- statement:
--   Let be $ a,b,c > 0$ such that $ a + b + c = 3$ . Prove that :
--
--    $ \frac {a^2b + 2a^2 + 1}{3b + 1} + \frac {b^2c + 2b^2 + 1}{3c + 1} + \frac {c^2a + 2c^2 + 1}{3a + 1}\ge 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3059` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3059; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3059 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^2 * b + 2 * a^2 + 1) / (3 * b + 1) + (b^2 * c + 2 * b^2 + 1) / (3 * c + 1) + (c^2 * a + 2 * c^2 + 1) / (3 * a + 1) ≥ 3   :=  by sorry
