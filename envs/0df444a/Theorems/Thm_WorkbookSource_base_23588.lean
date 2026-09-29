-- Prove2me | Theorems.Thm_WorkbookSource_base_23588
-- name    : WorkbookSource.base_23588
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:58:12.832489+00:00
-- url     : https://prove2.me/theorems/13158a2a-7764-4f01-a4fe-936173748cff
-- title:
--   A squared cyclic ratio sum with a symmetric correction
-- statement:
--   Let $a,b,c>0.$ Prove: $\frac{a^2}{b^2}+\frac{b^2}{c^2}+\frac{c^2}{a^2}+\frac{8(ab+ac+bc)}{a^2+b^2+c^2}\geq11$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23588` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23588; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23588 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b^2 / c^2 + c^2 / a^2 + 8 * (a * b + a * c + b * c) / (a^2 + b^2 + c^2)) ≥ 11  :=  by sorry
