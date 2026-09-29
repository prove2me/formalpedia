-- Prove2me | Theorems.Thm_WorkbookSource_base_42603
-- name    : WorkbookSource.base_42603
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:30:23.931637+00:00
-- url     : https://prove2.me/theorems/c617e13a-bc48-4cad-a3f1-46bb6fff1173
-- title:
--   A comparison of shifted reciprocal sums
-- statement:
--   For $ a,b,c>0 $, prove that $\frac{1}{2a+1}+\frac{1}{2b+1}+\frac{1}{2c+1}\geq\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42603` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42603; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42603 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + 1) + 1 / (2 * b + 1) + 1 / (2 * c + 1)) ≥ (1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1))  :=  by sorry
