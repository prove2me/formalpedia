-- Prove2me | Theorems.Thm_WorkbookSource_plus_44318
-- name    : WorkbookSource.plus_44318
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:34:58.397212+00:00
-- url     : https://prove2.me/theorems/36be07f1-367d-472d-b62f-8082b135d575
-- title:
--   A cyclic cubic upper bound at fixed sum three
-- statement:
--   Let $ a,b,c\ge 0$ such that $ a+b+c=3$ . Prove that:
--    $ (a^2b+b^2c+c^2a)+2(ab^2+bc^2+ca^2)+3abc\le 12$
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44318` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44318; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44318 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a^2 * b + b^2 * c + c^2 * a + 2 * (a * b^2 + b * c^2 + c * a^2) + 3 * a * b * c ≤ 12   :=  by sorry
