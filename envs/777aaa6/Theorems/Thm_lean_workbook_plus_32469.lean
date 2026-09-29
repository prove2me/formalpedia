-- Prove2me | Theorems.Thm_lean_workbook_plus_32469
-- name    : lean_workbook_plus_32469
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/36d69a0d-8d19-4dfb-bf3a-7270b3753351
-- statement:
--   ( a;b;c>0) \n $ \frac {a^2}{b} + \frac {b^2}{c} + \frac {c^2}{a}\ge \frac {a^2 + b^2 + c^2}{ab + ac + bc}(a + c + b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32469 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 / b + b^2 / c + c^2 / a) ≥ (a^2 + b^2 + c^2) / (a * b + b * c + a * c) * (a + b + c)   :=  by sorry
