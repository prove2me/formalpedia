-- Prove2me | Theorems.Thm_lean_workbook_plus_39572
-- name    : lean_workbook_plus_39572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/5fa053fd-6b45-432e-8cea-45c66fa62282
-- statement:
--   Find the maximum of $x^{2}+y^{2}+z^{2}$ given $0 \leq x,y,z\leq a$ and $x+y+z=m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39572 (x y z a m : ℝ) (hx : 0 ≤ x ∧ x ≤ a) (hy : 0 ≤ y ∧ y ≤ a) (hz : 0 ≤ z ∧ z ≤ a) (h : x + y + z = m) : (x^2 + y^2 + z^2) ≤ a^2 + a^2 + a^2   :=  by sorry
