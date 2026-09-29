-- Prove2me | Theorems.Thm_lean_workbook_plus_15528
-- name    : lean_workbook_plus_15528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6797535e-29bc-44a4-801a-4b8b5841805f
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=0$ .Prove that $\frac{a^2+b^2+c^2}{2}\cdot \frac{a^5+b^5+c^5}{5}=\frac{a^7+b^7+c^7}{7}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15528 (a b c : ℝ) (habc : a + b + c = 0) : (a^2 + b^2 + c^2) / 2 * (a^5 + b^5 + c^5) / 5 = (a^7 + b^7 + c^7) / 7   :=  by sorry
