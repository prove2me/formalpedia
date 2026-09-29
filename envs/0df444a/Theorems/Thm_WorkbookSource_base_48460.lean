-- Prove2me | Theorems.Thm_WorkbookSource_base_48460
-- name    : WorkbookSource.base_48460
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:41.038456+00:00
-- url     : https://prove2.me/theorems/8d5d197c-4c30-41b8-8c4a-5885da342fa5
-- title:
--   A quadratic reciprocal sum bounds two symmetric reciprocals
-- statement:
--   Let $a,b,c>0$ . Prove that $\sum_{cyc}\frac{1}{a^2+b^2}\geq\frac{1}{2(ab+ac+bc)}+\frac{4}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48460` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48460; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48460 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a ^ 2 + b ^ 2) + 1 / (b ^ 2 + c ^ 2) + 1 / (c ^ 2 + a ^ 2)) ≥ 1 / (2 * (a * b + a * c + b * c)) + 4 / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
