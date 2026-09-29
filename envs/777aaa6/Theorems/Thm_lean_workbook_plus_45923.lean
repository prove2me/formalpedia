-- Prove2me | Theorems.Thm_lean_workbook_plus_45923
-- name    : lean_workbook_plus_45923
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3a678902-324d-4c60-93d2-9be8cf30c7b2
-- statement:
--   Let $ a,b,c > 0,\;\;and \;\;a^2 + b^2 + c^2 = 1$ \nshow that: \n $ \frac {a}{b^2 + c^2} + \frac {b}{a^2 + c^2} + \frac {c}{a^2 + b^2}\geq\frac {3}{2}\sqrt {3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45923 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a / (b^2 + c^2) + b / (a^2 + c^2) + c / (a^2 + b^2) ≥ 3 / 2 * Real.sqrt 3   :=  by sorry
