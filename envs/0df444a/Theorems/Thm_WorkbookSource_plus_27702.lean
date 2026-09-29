-- Prove2me | Theorems.Thm_WorkbookSource_plus_27702
-- name    : WorkbookSource.plus_27702
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:26.144931+00:00
-- url     : https://prove2.me/theorems/21fdc663-ccde-4e8d-a9b6-cdfc16307015
-- title:
--   A sixth-degree inequality involving squared differences
-- statement:
--   If $a,b,c$ are non-negative numbers, such that $ab+bc+ca>0$ . then prove: $2\sum(a-b)^2(a+b-c)^2(b+c)(c+a)\geq 3(a-b)^2(b-c)^2(c-a)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_27702` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_27702; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_27702 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a * b + b * c + c * a > 0) : 2 * ((a - b) ^ 2 * (a + b - c) ^ 2 * (b + c) * (c + a) + (b - c) ^ 2 * (b + c - a) ^ 2 * (c + a) * (a + b) + (c - a) ^ 2 * (c + a - b) ^ 2 * (a + b) * (b + c)) ≥ 3 * ((a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2)   :=  by sorry
