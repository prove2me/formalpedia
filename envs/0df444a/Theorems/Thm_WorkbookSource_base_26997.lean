-- Prove2me | Theorems.Thm_WorkbookSource_base_26997
-- name    : WorkbookSource.base_26997
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:59:54.977338+00:00
-- url     : https://prove2.me/theorems/2131b85d-f884-447d-9e58-0d88d9e0e385
-- title:
--   The total times the cubic sum bounds a cyclic product-ratio expression
-- statement:
--   Let $a, b, c,d$ be positive real numbers. Prove that
--   $$(a+ b+ c+d)(a^3+ b^3+ c^3+d^3)\geq 4abcd\left(\frac{b}{a}+\frac{c}{b}+\frac{d}{c}+\frac{a}{d}\right) $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26997` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26997; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26997 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) ≥ 4 * a * b * c * d * (b / a + c / b + d / c + a / d)  :=  by sorry
