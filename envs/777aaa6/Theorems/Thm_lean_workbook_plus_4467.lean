-- Prove2me | Theorems.Thm_lean_workbook_plus_4467
-- name    : lean_workbook_plus_4467
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/88674846-2b6e-43f8-9137-95649f7e17ac
-- statement:
--   Prove that $ 2r \le R \Leftrightarrow 8xyz \le (x + y)(y + z)(z + x)$ using the Ravi Substitution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4467 (x y z r R : ℝ) (hx : x > 0 ∧ y > 0 ∧ z > 0) (hab : x + y + z = 1) (hbc : x + y = 2 * r) (hR : R = 2 * r * sin (π / 2)) : 2 * r ≤ R ↔ 8 * x * y * z ≤ (x + y) * (y + z) * (z + x)   :=  by sorry
