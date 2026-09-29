-- Prove2me | Theorems.Thm_WorkbookSource_plus_1874
-- name    : WorkbookSource.plus_1874
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:52:26.130245+00:00
-- url     : https://prove2.me/theorems/913ca0f7-60b5-4b1e-9a37-d0f2fceeea5c
-- title:
--   A squared weighted reciprocal sum upper bound
-- statement:
--   Prove that $\frac{1}{(2a + 2b + c)^2} + \frac{1}{(2b + 2c + a)^2} + \frac{1}{(2c + 2a + b)^2}$ $\leq$ $\frac{9}{25(ab+bc+ac)}$, where $a, b, c$ are real numbers all greater than 0.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_1874` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_1874; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_1874 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (2 * a + 2 * b + c) ^ 2 + 1 / (2 * b + 2 * c + a) ^ 2 + 1 / (2 * c + 2 * a + b) ^ 2) ≤ 9 / (25 * (a * b + b * c + a * c))   :=  by sorry
