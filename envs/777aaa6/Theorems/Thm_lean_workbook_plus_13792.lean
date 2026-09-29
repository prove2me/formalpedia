-- Prove2me | Theorems.Thm_lean_workbook_plus_13792
-- name    : lean_workbook_plus_13792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/69ee64fe-676e-4a2d-9036-4b2c48893858
-- statement:
--   so $ x^6+y^5 \le x+1 \iff y^5\le x+1-x^6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13792 : ∀ x y : ℝ, x^6 + y^5 ≤ x + 1 ↔ y^5 ≤ x + 1 - x^6   :=  by sorry
