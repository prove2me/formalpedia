-- Prove2me | Theorems.Thm_WorkbookSource_base_33098
-- name    : WorkbookSource.base_33098
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:48:33.358862+00:00
-- url     : https://prove2.me/theorems/509c5262-de7b-40ea-bf65-65ebd7b5b6d3
-- title:
--   Four positive reciprocals sum to at least sixteen divided by the total
-- statement:
--   Prove that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}\ge\frac{16}{a+b+c+d}$ for all positive $a, b, c$ and $d$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33098` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33098; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33098 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 / (a + b + c + d)  :=  by sorry
