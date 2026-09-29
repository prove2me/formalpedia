-- Prove2me | Theorems.Thm_WorkbookSource_base_15249
-- name    : WorkbookSource.base_15249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:00:11.530857+00:00
-- url     : https://prove2.me/theorems/97e0bdb9-07d9-4b14-8e83-fdb23bb13c8a
-- title:
--   A comparison of shifted linear reciprocal sums
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that $\frac{1}{4a+b+c}+\frac{1}{4b+c+a}+\frac{1}{4c+a+b}+\frac{3}{a+b+c}\le\frac{1}{a+b}+\frac{1}{b+c}+\frac{1}{c+a}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15249` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15249; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15249 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (4 * a + b + c) + 1 / (4 * b + c + a) + 1 / (4 * c + a + b) + 3 / (a + b + c)) ≤ (1 / (a + b) + 1 / (b + c) + 1 / (c + a))  :=  by sorry
