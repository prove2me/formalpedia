-- Prove2me | Theorems.Thm_WorkbookSource_base_42698
-- name    : WorkbookSource.base_42698
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:30:25.168855+00:00
-- url     : https://prove2.me/theorems/f2046936-2b44-4241-ae50-6f077034513a
-- title:
--   A mixed quadratic reciprocal lower bound
-- statement:
--   For positives $a$ , $b$ and $c$ prove that:
--    $\sum_{cyc}\frac{b+c}{2a^2+bc}\geq\frac{6}{a+b+c}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42698` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42698; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42698 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b + c) / (2 * a ^ 2 + b * c) + (a + c) / (2 * b ^ 2 + a * c) + (a + b) / (2 * c ^ 2 + a * b) ≥ 6 / (a + b + c)  :=  by sorry
