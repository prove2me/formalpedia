-- Prove2me | solution 1 for lean_workbook_plus_8556
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:06.440172+00:00
-- url     : https://prove2.me/submissions/9e02bfcf-33a4-4866-8749-5a8bec4a11be

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

theorem solution (a b : ℤ) (x0 : ℤ) (hx0 : x0 ≠ 0) (h : x0^2 + a * x0 + b = 0) : x0 ∣ b := by
  refine ⟨-(x0 + a), ?_⟩
  calc
    b = -(x0 ^ 2 + a * x0) := by linear_combination h
    _ = x0 * -(x0 + a) := by ring
