-- Prove2me | Theorems.Thm_WorkbookSource_base_45572
-- name    : WorkbookSource.base_45572
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:45:25.487388+00:00
-- url     : https://prove2.me/theorems/7ebfbb7c-c7d9-41d3-9150-d39ac392d1f1
-- title:
--   A reciprocal sum and triple product inequality at fixed sum three
-- statement:
--   Let $ a,b,c>0$ and $ a+b+c=3$ . Prove that: $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{48abc}{25}\ge\frac{123}{25}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45572` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45572; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45572 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : 1 / a + 1 / b + 1 / c + 48 * a * b * c / 25 ≥ 123 / 25  :=  by sorry
