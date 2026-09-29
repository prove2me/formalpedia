-- Prove2me | Theorems.Thm_lean_workbook_plus_66776
-- name    : lean_workbook_plus_66776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/7c390fcc-15e8-4872-9c3f-46c91dff41b5
-- statement:
--   Given $ a, b, c > 0$ and $ ab + bc + ca = 1$ . Prove that: $ (a^2 + 2b^2 + 3)(b^2 + 2c^2 + 3)(c^2 + 2a^2 + 3) \geq\ 64$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66776 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a * b + b * c + c * a = 1) :  (a^2 + 2 * b^2 + 3) * (b^2 + 2 * c^2 + 3) * (c^2 + 2 * a^2 + 3) ≥ 64   :=  by sorry
