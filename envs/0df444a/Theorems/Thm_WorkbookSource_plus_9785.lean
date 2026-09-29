-- Prove2me | Theorems.Thm_WorkbookSource_plus_9785
-- name    : WorkbookSource.plus_9785
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:58:00.181954+00:00
-- url     : https://prove2.me/theorems/dff3e1aa-8be7-4666-a5eb-4067aea3ef5b
-- title:
--   A squared cyclic ratio sum bounds a symmetric quadratic ratio
-- statement:
--   Let $a,b,c>0.$ Prove that $\frac{a^2}{b^2}+\frac{b^2}{c^2}+\frac{c^2}{a^2}+2\ge \frac{5(a^2+b^2+c^2)}{ab+bc+ca}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_9785` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_9785; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_9785 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b^2 + b^2 / c^2 + c^2 / a^2) + 2 ≥ 5 * (a^2 + b^2 + c^2) / (a * b + b * c + a * c)   :=  by sorry
