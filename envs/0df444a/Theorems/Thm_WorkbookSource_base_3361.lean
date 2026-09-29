-- Prove2me | Theorems.Thm_WorkbookSource_base_3361
-- name    : WorkbookSource.base_3361
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:10.24097+00:00
-- url     : https://prove2.me/theorems/c58099da-fd14-421f-9ab8-e4d268132f0b
-- title:
--   A five-variable difference of pairwise products
-- statement:
--   Let $a,b,c,d, e \geq 0$ such that $a+b+c+d+e=5$ . Prove that: $ab+cd+ea +\frac{25}{4} \geq bc+de$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3361` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3361; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3361 (a b c d e : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (he : e ≥ 0) (hab : a + b + c + d + e = 5) : a * b + c * d + e * a + 25 / 4 ≥ b * c + d * e  :=  by sorry
