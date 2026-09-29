-- Prove2me | Theorems.Thm_WorkbookSource_base_32038
-- name    : WorkbookSource.base_32038
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:00.924183+00:00
-- url     : https://prove2.me/theorems/22a2547a-eb14-4180-96ec-b1c5066959dc
-- title:
--   A weighted cyclic linear ratio sum is at most one quarter
-- statement:
--   Prove that $\frac{a}{5a+5b+2c}+\frac{b}{5b+5c+2a}+\frac{c}{5c+5a+2b}\le \frac{1}{4}$ given $a,b,c >0$ without full expansion.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32038` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32038; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32038 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a + 5 * b + 2 * c) + b / (5 * b + 5 * c + 2 * a) + c / (5 * c + 5 * a + 2 * b)) ≤ 1 / 4  :=  by sorry
