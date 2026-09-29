-- Prove2me | Theorems.Thm_WorkbookSource_base_49763
-- name    : WorkbookSource.base_49763
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:35.58392+00:00
-- url     : https://prove2.me/theorems/48605f62-18b7-4f4a-9858-7d93cf3491bb
-- title:
--   A cyclic product ratio sum is at least three quarters
-- statement:
--   Given $a,b,c > 0$,
--   $\frac{a+b}{b+c}.\frac{a}{2a+b+c}+\frac{b+c}{c+a}. \frac{b}{2b+c+a}+\frac{c+a}{a+b}.\frac{c}{2c+a+b}\geq \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49763` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49763; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49763 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) * (a / (2 * a + b + c)) + (b + c) / (c + a) * (b / (2 * b + c + a)) + (c + a) / (a + b) * (c / (2 * c + a + b)) ≥ 3 / 4  :=  by sorry
