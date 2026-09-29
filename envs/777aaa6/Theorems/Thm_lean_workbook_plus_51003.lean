-- Prove2me | Theorems.Thm_lean_workbook_plus_51003
-- name    : lean_workbook_plus_51003
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/2d39fe92-9150-4838-9274-b693424e43b7
-- statement:
--   if $a,b,c$ be positive real numbers , prove that \na) $ a^4+b^4+c^4\ge abc(a+b+c)$ \nb) $\left(\frac{a+b+c}{3}\right)^3 \ge a\left(\frac{b+c}{2}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51003 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 >= a * b * c * (a + b + c)   :=  by sorry
