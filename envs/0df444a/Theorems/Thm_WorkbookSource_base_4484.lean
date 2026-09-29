-- Prove2me | Theorems.Thm_WorkbookSource_base_4484
-- name    : WorkbookSource.base_4484
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:24:20.511876+00:00
-- url     : https://prove2.me/theorems/25cfacb3-80e3-4324-a0bb-9a0aa3116f16
-- title:
--   A squared reciprocal sum bounds quadratic reciprocal terms
-- statement:
--   Let $a,b,c$ be three positive real numbers , prove that $(\frac{1}{a}+\frac{1}{b}+\frac{1}{c})^2\ge\frac{1}{a^2}+\frac{4}{b^2+c^2}+\frac{18}{a^2+b^2+c^2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4484` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4484; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4484 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (1 / a + 1 / b + 1 / c) ^ 2 ≥ 1 / a ^ 2 + 4 / (b ^ 2 + c ^ 2) + 18 / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
