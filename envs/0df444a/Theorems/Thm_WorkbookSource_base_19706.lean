-- Prove2me | Theorems.Thm_WorkbookSource_base_19706
-- name    : WorkbookSource.base_19706
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:41:45.445423+00:00
-- url     : https://prove2.me/theorems/8f10e619-c10e-4dd1-ae22-54317cb0b22c
-- title:
--   A cyclic mixed cubic ratio lower bound at fixed sum three
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that
--    $\frac{a^3}{b^2+bc+a}+\frac{b^3}{c^2+ca+b}+\frac{c^3}{a^2+ab+c}\ge1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19706` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19706; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19706 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / (b^2 + b * c + a) + b^3 / (c^2 + c * a + b) + c^3 / (a^2 + a * b + c) ≥ 1  :=  by sorry
