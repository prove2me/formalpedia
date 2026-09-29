-- Prove2me | Theorems.Thm_WorkbookSource_plus_25220
-- name    : WorkbookSource.plus_25220
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:25.357172+00:00
-- url     : https://prove2.me/theorems/b232b2f0-aaf8-4364-8792-48d2f3011769
-- title:
--   A symmetric ratio sum bounds an asymmetric pairwise expression
-- statement:
--   Let $a, b, c$ be positive real numbers. Prove that $\frac{a+b}{c}+\frac{b+c}{a}+\frac{c+a}{b}\ge \frac{2a}{b+c}+\frac{b+c}{a+b}+\frac{b+c}{a+c}+3$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_25220` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_25220; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_25220 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / c + (b + c) / a + (c + a) / b ≥ 2 * a / (b + c) + (b + c) / (a + b) + (b + c) / (a + c) + 3   :=  by sorry
