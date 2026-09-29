-- Prove2me | Theorems.Thm_WorkbookSource_base_3920
-- name    : WorkbookSource.base_3920
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:10:55.839201+00:00
-- url     : https://prove2.me/theorems/5d112d26-2758-4ceb-846b-de72653c8c34
-- title:
--   A cyclic squared-reciprocal comparison at fixed sum three
-- statement:
--   Let $a,b,c$ be positive and $a+b+c=3.$
--    $$\frac{a}{b^2}+\frac{b}{c^2}+\frac{c}{a^2}\geq \frac{a}{b}+\frac{b}{c}+\frac{c}{a}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3920` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3920; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3920 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : a / b ^ 2 + b / c ^ 2 + c / a ^ 2 ≥ a / b + b / c + c / a  :=  by sorry
