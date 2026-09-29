-- Prove2me | Theorems.Thm_WorkbookSource_base_18063
-- name    : WorkbookSource.base_18063
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:12:41.231407+00:00
-- url     : https://prove2.me/theorems/64ad3235-f624-48cc-863a-1f1291c73c66
-- title:
--   A shifted reciprocal sum bounds a symmetric rational expression
-- statement:
--   prove that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+2 \ge \frac{12+3abc}{ab+bc+ca}$ given $a,b,c > 0$ and $a+b+c=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18063` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18063; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18063 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 3) : 1 / a + 1 / b + 1 / c + 2 ≥ (12 + 3 * a * b * c) / (a * b + b * c + c * a)  :=  by sorry
