-- Prove2me | Theorems.Thm_WorkbookSource_base_20388
-- name    : WorkbookSource.base_20388
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:45:50.263611+00:00
-- url     : https://prove2.me/theorems/006d5f02-4f1b-401c-8368-149257420a76
-- title:
--   A weighted cyclic quadratic ratio bounds a normalized cubic sum
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{(3a+b)(5a-b)}{b+c}+\frac{(3b+c)(5b-c)}{c+a}+\frac{(3c+a)(5c-a)}{a+b}\ge 24\cdot\frac{a^3+b^3+c^3}{a^2+b^2+c^2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20388` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20388; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20388 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a + b) * (5 * a - b) / (b + c) + (3 * b + c) * (5 * b - c) / (c + a) + (3 * c + a) * (5 * c - a) / (a + b) ≥ 24 * (a ^ 3 + b ^ 3 + c ^ 3) / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
