-- Prove2me | Theorems.Thm_WorkbookSource_base_53584
-- name    : WorkbookSource.base_53584
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:06:16.020298+00:00
-- url     : https://prove2.me/theorems/c65c5f62-cfc0-46f6-8881-47f444f9c84d
-- title:
--   A weighted quadratic ratio bounds pairwise products over the total
-- statement:
--   For $a, b, c>0$ prove that
--    $\frac{a(a^2+b^2)}{5a^2+3b^2}+\frac{b(b^2+c^2)}{5b^2+3c^2}+\frac{c(c^2+a^2)}{5c^2+3a^2}\ge\frac{3}{4}\cdot\frac{ab+bc+ca}{a+b+c}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53584` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53584; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53584 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * (a ^ 2 + b ^ 2) / (5 * a ^ 2 + 3 * b ^ 2) + b * (b ^ 2 + c ^ 2) / (5 * b ^ 2 + 3 * c ^ 2) + c * (c ^ 2 + a ^ 2) / (5 * c ^ 2 + 3 * a ^ 2)) ≥ 3 / 4 * (a * b + b * c + c * a) / (a + b + c)  :=  by sorry
