-- Prove2me | Theorems.Thm_WorkbookSource_base_33362
-- name    : WorkbookSource.base_33362
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:51:49.037805+00:00
-- url     : https://prove2.me/theorems/c5d60953-5479-42e5-834b-192a6902711c
-- title:
--   A symmetric quadratic ratio with a cubic reciprocal correction
-- statement:
--   Let $a,b,c>0$. Prove that $\frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{1}{8}.\frac{(a+b)(b+c)(c+a)}{a^3+b^3+c^3}\geq \frac{4}{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33362` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33362; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33362 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (1 / 8) * ((a + b) * (b + c) * (c + a)) / (a^3 + b^3 + c^3) ≥ 4 / 3  :=  by sorry
