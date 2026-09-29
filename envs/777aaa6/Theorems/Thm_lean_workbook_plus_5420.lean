-- Prove2me | Theorems.Thm_lean_workbook_plus_5420
-- name    : lean_workbook_plus_5420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/2a0a87d6-f1f7-4e08-a03a-06443b28a295
-- statement:
--   Let $a,b>0. $ Prove that $$ \frac{a^5+2b^5}{a^2+2b^2}+\frac{a^4+2b^4}{a+2b}\geq \frac{2}{3}(a^3+2b^3)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5420 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^5 + 2 * b^5) / (a^2 + 2 * b^2) + (a^4 + 2 * b^4) / (a + 2 * b) ≥ 2 / 3 * (a^3 + 2 * b^3)   :=  by sorry
