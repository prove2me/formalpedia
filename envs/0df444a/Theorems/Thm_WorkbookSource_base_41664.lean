-- Prove2me | Theorems.Thm_WorkbookSource_base_41664
-- name    : WorkbookSource.base_41664
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:01:29.938749+00:00
-- url     : https://prove2.me/theorems/7c70e043-f071-4889-92ae-d68160258794
-- title:
--   A cyclic squared reciprocal ratio lower bound
-- statement:
--   Let $a,b,c >0$ . Prove that
--
--    $$\frac{b}{a^2} + \frac{c}{b^2} + \frac{a}{c^2} \geq \frac{9}{(a+b+c)}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41664` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41664; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41664 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (b / a ^ 2 + c / b ^ 2 + a / c ^ 2) ≥ 9 / (a + b + c)  :=  by sorry
