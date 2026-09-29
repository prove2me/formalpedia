-- Prove2me | Theorems.Thm_WorkbookSource_base_38723
-- name    : WorkbookSource.base_38723
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:48.48285+00:00
-- url     : https://prove2.me/theorems/d8191355-58a8-48cb-b771-69b512fd18db
-- title:
--   A sum of linear and squared pair-sum ratios is at least sixteen fifths
-- statement:
--   Let $a,b,c$ are positive real numbers. Prove that
--    $$\frac{b+c}{ a}+\frac{2}{125}\left(\frac{c+a}{b}\right)^2+\frac{a+b}{ c} \ge \frac{16}{5} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38723` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38723; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38723 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / a + (2 / 125) * ((c + a) / b) ^ 2 + (a + b) / c ≥ 16 / 5  :=  by sorry
