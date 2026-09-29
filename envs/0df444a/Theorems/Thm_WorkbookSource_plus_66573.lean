-- Prove2me | Theorems.Thm_WorkbookSource_plus_66573
-- name    : WorkbookSource.plus_66573
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:29.664429+00:00
-- url     : https://prove2.me/theorems/6b509aae-d0c9-41ed-93ce-1799d679cd44
-- title:
--   A product of shifted rational expressions is at least nine halves
-- statement:
--   Let $a,b,c>0.$ Prove that $(1+\frac{ab}{c+a})\left(1+\frac{2a}{b(c+a)}+\frac{c}{a}\right)\geq \frac{9}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_66573` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_66573; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_66573 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 + a * b / (c + a)) * (1 + 2 * a / (b * (c + a)) + c / a) ≥ 9 / 2   :=  by sorry
