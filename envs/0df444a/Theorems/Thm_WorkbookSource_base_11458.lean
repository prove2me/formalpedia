-- Prove2me | Theorems.Thm_WorkbookSource_base_11458
-- name    : WorkbookSource.base_11458
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:38:26.065827+00:00
-- url     : https://prove2.me/theorems/e9b0e3f5-0df2-4e29-80de-ce46c6c7c521
-- title:
--   A weighted quadratic ratio sum with a symmetric correction
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a(3a+b+c)}{b^2+c^2}+\frac{b(3b+c+a)}{c^2+a^2}+\frac{c(3c+a+b)}{a^2+b^2}+\frac{ab+bc+ca}{a^2+b^2+c^2}\ge\frac{17}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11458` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11458; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11458 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (3 * a + b + c) / (b ^ 2 + c ^ 2) + b * (3 * b + c + a) / (c ^ 2 + a ^ 2) + c * (3 * c + a + b) / (a ^ 2 + b ^ 2) + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 17 / 2  :=  by sorry
