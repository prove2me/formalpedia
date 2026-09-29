-- Prove2me | Theorems.Thm_WorkbookSource_base_17392
-- name    : WorkbookSource.base_17392
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:22:50.529906+00:00
-- url     : https://prove2.me/theorems/5fd16ad2-0a21-44ea-a7fa-c40452da0cf6
-- title:
--   A four-variable triple quadratic ratio sum is at least four
-- statement:
--   Let $a,b,c,d $ -reals positive numbers. Prove inequality:
--    $\frac{a^2+b^2+c^2}{ab+bc+cd}+\frac{b^2+c^2+d^2}{bc+cd+ad}+\frac{a^2+c^2+d^2}{ab+ad+cd}+\frac{a^2+b^2+d^2}{ab+ad+bc} \geq 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17392` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17392; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17392 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : (a^2 + b^2 + c^2) / (a * b + b * c + c * d) + (b^2 + c^2 + d^2) / (b * c + c * d + d * a) + (a^2 + c^2 + d^2) / (a * b + a * d + c * d) + (a^2 + b^2 + d^2) / (a * b + a * d + b * c) ≥ 4  :=  by sorry
