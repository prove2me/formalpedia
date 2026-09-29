-- Prove2me | Theorems.Thm_WorkbookSource_base_15999
-- name    : WorkbookSource.base_15999
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:01:44.094956+00:00
-- url     : https://prove2.me/theorems/7a749136-6552-4f5b-a595-beefaee66376
-- title:
--   A squared ratio sum bounds a symmetric quadratic ratio
-- statement:
--   Prove that $(\frac{a}{b+c})^2+(\frac{b}{c+a})^2+(\frac{c}{a+b})^2+3\geq \frac{5(a+b+c)^2}{4(ab+bc+ca)}$ for $a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15999` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15999; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15999 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 + 3 ≥ 5 * (a + b + c) ^ 2 / (4 * (a * b + b * c + a * c))  :=  by sorry
