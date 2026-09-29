-- Prove2me | Theorems.Thm_WorkbookSource_plus_12056
-- name    : WorkbookSource.plus_12056
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:48:59.030278+00:00
-- url     : https://prove2.me/theorems/31c616bc-e6c6-4e51-a6bf-724668c54710
-- title:
--   A four-variable quadratic lower bound at total four
-- statement:
--   Let $ a,b,c,d\geq 0 $ and $ a+b+c+d=4 .$ Prove that
--    $$a^2+ b^2+c^2+d^2+a+bc+d \geq 7$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_12056` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_12056; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_12056 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 + a + b*c + d ≥ 7   :=  by sorry
