-- Prove2me | Theorems.Thm_lean_workbook_plus_25909
-- name    : lean_workbook_plus_25909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b614529b-198b-4f00-8c1c-156550739c4c
-- statement:
--   Prove that, for $ a$ , $ b$ , $ c > 0$ , $ \frac {a^3 + b^3 + c^3}{a^2 + b^2 + c^2} \ge \frac {a + b + c}{3}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25909 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a^2 + b^2 + c^2) ≥ (a + b + c) / 3   :=  by sorry
