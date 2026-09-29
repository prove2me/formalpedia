-- Prove2me | Theorems.Thm_lean_workbook_plus_33427
-- name    : lean_workbook_plus_33427
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/284f8705-45eb-40a7-9601-9d5059777b02
-- statement:
--   Let $a,b,c>0$ : $a^2+ab+b^2=1$ . Prove that: \n $\sqrt{a+b}+\sqrt[4]{ab}\leq \frac{\sqrt{2}+1}{\sqrt[4]{3}}$ (George Apostolopoulos )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33427 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b * c = 1) : a^2 + a * b + b^2 = 1 → Real.sqrt (a + b) + (ab)^(1 / 4) ≤ (Real.sqrt 2 + 1) / (3)^(1 / 4)   :=  by sorry
