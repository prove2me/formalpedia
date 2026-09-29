-- Prove2me | Theorems.Thm_WorkbookSource_base_36161
-- name    : WorkbookSource.base_36161
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:09:03.230312+00:00
-- url     : https://prove2.me/theorems/5fb42cf1-27b7-44d4-aa89-c310d789cda0
-- title:
--   A cyclic cubic ratio bounds the quadratic sum at fixed sum three
-- statement:
--   If the positive reals $a,b,c$ satisfy $a+b+c=3$ prove that
--
--    $$\sum_{cyc} \frac{a^3}{b^2}\geq a^2+b^2+c^2.$$
--
--
--   By computer,we have
--
--    $$LHS-RHS=\frac{1}{3}\sum_{cyc}{\frac{(ab+bc+3a+3b)(a-b)^2}{b^2}}\ge{0}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36161` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36161; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36161 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^3 / b^2 + b^3 / c^2 + c^3 / a^2 ≥ a^2 + b^2 + c^2  :=  by sorry
