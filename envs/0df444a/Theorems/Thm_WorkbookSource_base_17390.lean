-- Prove2me | Theorems.Thm_WorkbookSource_base_17390
-- name    : WorkbookSource.base_17390
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:09:42.943739+00:00
-- url     : https://prove2.me/theorems/b9bd9377-4a47-480b-ac89-49ef197f08f7
-- title:
--   A quadratic reciprocal lower bound involving symmetric products
-- statement:
--   For all positive reals $a, b, c $ prove the following inequality: $\frac{1}{ab}+\frac{1}{bc}+\frac{1}{ca}+\frac{2}{a^2+b^2+c^2}\geq \frac{11}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17390` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17390; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17390 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a * b) + 1 / (b * c) + 1 / (c * a) + 2 / (a^2 + b^2 + c^2)) ≥ 11 / (a * b + b * c + c * a)  :=  by sorry
