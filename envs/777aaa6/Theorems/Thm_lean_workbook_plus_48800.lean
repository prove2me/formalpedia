-- Prove2me | Theorems.Thm_lean_workbook_plus_48800
-- name    : lean_workbook_plus_48800
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e30f972e-ec65-4ab7-b456-aa895397368b
-- statement:
--   Using Euclid's algorithm, find $g.c.d.(6893, 11 639)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48800 (a b : ℕ) (h₁ : a = 6893) (h₂ : b = 11639) : Nat.gcd a b = 113   :=  by sorry
