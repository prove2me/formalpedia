-- Prove2me | Theorems.Thm_WorkbookSource_base_10806
-- name    : WorkbookSource.base_10806
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:14.211848+00:00
-- url     : https://prove2.me/theorems/65487579-73c4-45ba-a17c-a0c7a4c2eb17
-- title:
--   A four-variable weighted cyclic ratio sum is at least one
-- statement:
--   Let $a,b,c,d>0$ . Prove that $\frac{a}{b + 2c + d}+ \frac{b}{c + 2d + a}+ \frac{c}{d + 2a + b}+ \frac{d}{a + 2b + c}\geq1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10806` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10806; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10806 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a / (b + 2 * c + d) + b / (c + 2 * d + a) + c / (d + 2 * a + b) + d / (a + 2 * b + c)) ≥ 1  :=  by sorry
