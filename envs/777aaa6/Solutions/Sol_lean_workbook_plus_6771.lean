-- Prove2me | solution 1 for lean_workbook_plus_6771
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:50:06.514849+00:00
-- url     : https://prove2.me/submissions/dadfe431-5d86-4358-a916-2f8888354fbc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (n m : ℤ) (p : ℕ) (hp : p.Prime) (h : n = m * p) : (n + p^2) / p = m + p := by
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast hp.ne_zero
  rw [h]
  have he : m*(p:ℤ)+(p:ℤ)^2=(m+p)*p := by ring
  rw [he,Int.mul_ediv_cancel _ hp0]
