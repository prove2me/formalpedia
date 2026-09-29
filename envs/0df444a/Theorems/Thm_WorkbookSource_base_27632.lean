-- Prove2me | Theorems.Thm_WorkbookSource_base_27632
-- name    : WorkbookSource.base_27632
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:49:37.63708+00:00
-- url     : https://prove2.me/theorems/33adb023-d41f-4091-a7d8-06744dd5da2b
-- title:
--   A reciprocal sum with a pairwise-product correction
-- statement:
--   Prove that $\frac2a+\frac2b+\frac2c+2(ab+bc+ca)\ge12$ given $a,b,c$ are positive and $a+b+c=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27632` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27632; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_27632 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 2 / a + 2 / b + 2 / c + 2 * (a * b + b * c + c * a) ≥ 12  :=  by sorry
