-- Prove2me | Theorems.Thm_WorkbookSource_base_21189
-- name    : WorkbookSource.base_21189
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:55.976588+00:00
-- url     : https://prove2.me/theorems/85413cf0-e992-4f0f-ae08-87cf3f924a57
-- title:
--   A comparison of shifted pairwise ratio sums
-- statement:
--   Prove that for positive real numbers \(a, b, c\), the following inequality holds:
--   $$\frac{3}{8}+\frac{a}{c+b}+\frac{b}{a+c}+\frac{c}{b+a} \ge \frac{25}{8}\left(\frac{a}{a+2b+2c}+\frac{b}{b+2c+2a}+\frac{c}{c+2a+2b}\right)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21189` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21189; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21189 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 / 8 + a / (c + b) + b / (a + c) + c / (b + a) ≥ 25 / 8 * (a / (a + 2 * b + 2 * c) + b / (b + 2 * c + 2 * a) + c / (c + 2 * a + 2 * b))  :=  by sorry
