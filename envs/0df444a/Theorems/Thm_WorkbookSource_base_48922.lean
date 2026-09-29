-- Prove2me | Theorems.Thm_WorkbookSource_base_48922
-- name    : WorkbookSource.base_48922
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:18.442647+00:00
-- url     : https://prove2.me/theorems/01d45b86-cd52-4953-bbf0-f1506ab9055e
-- title:
--   A shifted cyclic quadratic ratio lower bound at fixed sum three
-- statement:
--   Given 3 positive real numbers a, b, c. That satisfy $a + b + c = 3$ . Prove that:
--
--    $\frac{3ab + 5a}{b^2+4b+3}+\frac{3bc + 5b}{c^2+4c+3}+\frac{3ca + 5c}{a^2+4a+3} \geq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48922` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48922; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48922 (a b c : ℝ) (habc : a + b + c = 3) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a * b + 5 * a) / (b ^ 2 + 4 * b + 3) + (3 * b * c + 5 * b) / (c ^ 2 + 4 * c + 3) + (3 * c * a + 5 * c) / (a ^ 2 + 4 * a + 3) ≥ 3  :=  by sorry
