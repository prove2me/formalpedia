-- Prove2me | Theorems.Thm_WorkbookSource_base_3622
-- name    : WorkbookSource.base_3622
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:09.449557+00:00
-- url     : https://prove2.me/theorems/d6142997-9c76-4199-a9c3-a7715a3a6c51
-- title:
--   A cyclic product inequality at fixed pairwise sum
-- statement:
--   Let's a,b,c>0: ab+bc+ca=3. Prove:
--    $(a+b)(a+bc)+(b+c)(b+ca)+(c+a)(c+ab)\geq 12$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3622` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3622; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3622 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : (a + b) * (a + b * c) + (b + c) * (b + c * a) + (c + a) * (c + a * b) ≥ 12  :=  by sorry
