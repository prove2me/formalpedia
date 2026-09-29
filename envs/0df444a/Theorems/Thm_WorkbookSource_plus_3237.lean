-- Prove2me | Theorems.Thm_WorkbookSource_plus_3237
-- name    : WorkbookSource.plus_3237
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:47.661791+00:00
-- url     : https://prove2.me/theorems/bce08296-bce3-4552-a77d-54426f2a3609
-- title:
--   An eighth-degree inequality involving squared pairwise differences
-- statement:
--   For non-negative numbers $a, b, c$, prove that $3\sum (a-b)^2(a+b-c)^2(a^2+ac+c^2)(b^2+bc+c^2) \geq 4 (a+b+c)^2(a-b)^2(b-c)^2(c-a)^2$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_3237` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_3237; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_3237 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * ((a - b) ^ 2 * (a + b - c) ^ 2 * (a ^ 2 + a * c + c ^ 2) * (b ^ 2 + b * c + c ^ 2) + (b - c) ^ 2 * (b + c - a) ^ 2 * (b ^ 2 + b * a + a ^ 2) * (c ^ 2 + c * a + a ^ 2) + (c - a) ^ 2 * (c + a - b) ^ 2 * (c ^ 2 + c * b + b ^ 2) * (a ^ 2 + a * b + b ^ 2)) ≥ 4 * (a + b + c) ^ 2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2   :=  by sorry
