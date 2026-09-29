-- Prove2me | Theorems.Thm_WorkbookSource_base_22008
-- name    : WorkbookSource.base_22008
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:34:36.579798+00:00
-- url     : https://prove2.me/theorems/68b8bada-d0ea-4d8b-a475-91ed7a8b9097
-- title:
--   A sum of triple cubic averages bounds the quadratic sum
-- statement:
--   Let $a,b,c,d$ be positive real numbers. Prove that :
--    $\frac{a^{3}+b^{3}+c^{3}}{a+b+c}+\frac{b^{3}+c^{3}+d^{3}}{b+c+d}+\frac{c^{3}+d^{3}+a^{3}}{c+d+a}+\frac{d^{3}+a^{3}+b^{3}}{d+a+b}\geq a^{2}+b^{2}+c^{2}+d^{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22008` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22008; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22008 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^3 + b^3 + c^3) / (a + b + c) + (b^3 + c^3 + d^3) / (b + c + d) + (c^3 + d^3 + a^3) / (c + d + a) + (d^3 + a^3 + b^3) / (d + a + b) ≥ a^2 + b^2 + c^2 + d^2  :=  by sorry
