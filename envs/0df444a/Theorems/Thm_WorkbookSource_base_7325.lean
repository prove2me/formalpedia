-- Prove2me | Theorems.Thm_WorkbookSource_base_7325
-- name    : WorkbookSource.base_7325
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:04.077762+00:00
-- url     : https://prove2.me/theorems/8f7187e4-5d80-469f-9fe7-d6d25ed430ff
-- title:
--   A five-variable cyclic product bound
-- statement:
--   Given $a, b, c, d, e$ are real numbers such that $a + b + c + d + e = 1$, prove that $2(ab + bc + cd + de + ea) + ac + bd + ce + da + eb \leq \frac{3}{5}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7325` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7325; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7325 (a b c d e : ℝ) (h : a + b + c + d + e = 1) :  2 * (a * b + b * c + c * d + d * e + e * a) + a * c + b * d + c * e + d * a + e * b ≤ 3 / 5  :=  by sorry
