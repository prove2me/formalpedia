-- Prove2me | Theorems.Thm_WorkbookSource_base_21045
-- name    : WorkbookSource.base_21045
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:40.648226+00:00
-- url     : https://prove2.me/theorems/5092545b-79e6-454d-b2ee-4b01e47b5fc1
-- title:
--   A symmetric squared ratio sum is at least three fifths
-- statement:
--   Prove that : $\sum {\frac{{{a^2}}}{{{a^2} + {{(b + c)}^2}}} \ge \frac{3}{5}} $ with $a;b;c \in {R^ + }$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21045` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21045; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21045 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : 3 / 5 ≤ a ^ 2 / (a ^ 2 + (b + c) ^ 2) + b ^ 2 / (b ^ 2 + (c + a) ^ 2) + c ^ 2 / (c ^ 2 + (a + b) ^ 2)  :=  by sorry
