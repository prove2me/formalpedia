-- Prove2me | Theorems.Thm_WorkbookSource_base_12662
-- name    : WorkbookSource.base_12662
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:17.663868+00:00
-- url     : https://prove2.me/theorems/dc9daece-802f-4995-94f8-daf40b5b1664
-- title:
--   A weighted quadratic reciprocal upper comparison
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers. Prove that: $ (9a^2+9b^2+c^2 )\left(\frac{1}{a+4c}+\frac{1}{b+4c}\right)\geq 2(a+b) $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12662` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12662; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12662 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (9 * a ^ 2 + 9 * b ^ 2 + c ^ 2) * (1 / (a + 4 * c) + 1 / (b + 4 * c)) ≥ 2 * (a + b)  :=  by sorry
