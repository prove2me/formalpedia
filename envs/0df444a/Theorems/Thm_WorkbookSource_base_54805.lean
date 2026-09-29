-- Prove2me | Theorems.Thm_WorkbookSource_base_54805
-- name    : WorkbookSource.base_54805
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:34.774865+00:00
-- url     : https://prove2.me/theorems/e3907a16-bef9-4c4d-b078-c461f6c54c3b
-- title:
--   A reciprocal pair-product sum correction bounds eight divided by the total
-- statement:
--   Let $a, b, c, d$ be positive real numbers. Prove that $1+\frac{6}{ab+ac+ad+bc+bd+cd}\geq\frac{8}{a+b+c+d},$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54805` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54805; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54805 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 8 / (a + b + c + d)  :=  by sorry
