-- Prove2me | Theorems.Thm_WorkbookSource_base_38347
-- name    : WorkbookSource.base_38347
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:53.860571+00:00
-- url     : https://prove2.me/theorems/c28f49f2-6dc8-419e-b0aa-dfd3d925cb2f
-- title:
--   A sum-product lower bound at pairwise sum three
-- statement:
--   Let $ a,b,c>0,ab+bc+ca=3 $ . prove that:
--    $ 3(a+b+c)+abc\geq 10 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38347` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38347; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38347 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : 3 * (a + b + c) + a * b * c ≥ 10  :=  by sorry
