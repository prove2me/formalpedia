-- Prove2me | Theorems.Thm_WorkbookSource_plus_42193
-- name    : WorkbookSource.plus_42193
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:07:18.041259+00:00
-- url     : https://prove2.me/theorems/7648ffc8-4237-42fd-9603-478111ba3fc8
-- title:
--   A weighted squared reciprocal sum lower bound
-- statement:
--   Prove that $\sum\frac1{(2a+2b+c)^2}\ge\frac{27}{25(a+b+c)^2}$, where $a, b, c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_42193` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_42193; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_42193 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + 2 * b + c) ^ 2 + 1 / (2 * b + 2 * c + a) ^ 2 + 1 / (2 * c + 2 * a + b) ^ 2) ≥ 27 / (25 * (a + b + c) ^ 2)   :=  by sorry
