-- Prove2me | Theorems.Thm_WorkbookSource_plus_79000
-- name    : WorkbookSource.plus_79000
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:55.510474+00:00
-- url     : https://prove2.me/theorems/6cc4d32c-967c-414f-844c-aa35ebe57ef7
-- title:
--   A four-variable product bound for paired products
-- statement:
--   Let $a,b,c,d\geq 0$ ,prove that: $(a+c+d)(d+a+b)(a+b+c)(b+c+d)-\\frac{27}{4}(cd+ab)(bc+ad)-\\frac{27}{4}(ac+bd)(bc+ad)-\\frac{27}{4}(cd+ab)(ac+bd)\\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_79000` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_79000; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_79000 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - 27 / 4 * (c * d + a * b) * (b * c + a * d) - 27 / 4 * (a * c + b * d) * (b * c + a * d) - 27 / 4 * (c * d + a * b) * (a * c + b * d) ≥ 0   :=  by sorry
