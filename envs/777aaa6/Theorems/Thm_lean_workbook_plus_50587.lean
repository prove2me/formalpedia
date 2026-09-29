-- Prove2me | Theorems.Thm_lean_workbook_plus_50587
-- name    : lean_workbook_plus_50587
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/d237dc56-d13a-40f6-8e20-ded424e059d6
-- statement:
--   $ \frac {a^2}{a^2 + ab + b^2} + \frac {b^2}{b^2 + bc + c^2} + \frac {c^2}{c^2 + ca + a^2} + \frac {ab + bc + ca}{a^2 + b^2 + c^2}\leq 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50587 : ∀ a b c : ℝ, (a^2 / (a^2 + a * b + b^2) + b^2 / (b^2 + b * c + c^2) + c^2 / (c^2 + c * a + a^2) + (a * b + b * c + c * a) / (a^2 + b^2 + c^2) ≤ 2)   :=  by sorry
