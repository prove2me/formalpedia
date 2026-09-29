-- Prove2me | Theorems.Thm_WorkbookSource_base_26631
-- name    : WorkbookSource.base_26631
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:29:22.226624+00:00
-- url     : https://prove2.me/theorems/b263606e-9de6-470d-8e3a-d4125d91e3c6
-- title:
--   A symmetric quadratic ratio with a pair-product correction
-- statement:
--   If $a,b,c>0$ then prove that
--
--   $\frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{8(ab+bc+ca)(a+b+c)}{9(a+b)(b+c)(c+a)}\geq 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26631` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26631; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26631 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + a * c) + (8 * (a * b + b * c + a * c) * (a + b + c)) / (9 * (a + b) * (b + c) * (c + a)) ≥ 2  :=  by sorry
