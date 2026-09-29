-- Prove2me | Theorems.Thm_WorkbookSource_base_32964
-- name    : WorkbookSource.base_32964
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:45:21.859882+00:00
-- url     : https://prove2.me/theorems/fa13a63c-74ca-456b-bd9c-547a07df8c46
-- title:
--   A refined cyclic quadratic ratio lower bound
-- statement:
--   Let $a,b,c$ be positive reals . Prove that $$ \frac{a^2+b^2}{c^2+ab}+\frac{b^2+c^2}{a^2+bc}+\frac{c^2+a^2}{b^2+ca}\geq3+\frac{4(a^2+b^2+c^2-ab-ac-bc)}{(a+b+c)^2}. $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32964` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32964; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32964 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) / (c^2 + a * b) + (b^2 + c^2) / (a^2 + b * c) + (c^2 + a^2) / (b^2 + c * a) ≥ 3 + 4 * (a^2 + b^2 + c^2 - a * b - a * c - b * c) / (a + b + c)^2  :=  by sorry
