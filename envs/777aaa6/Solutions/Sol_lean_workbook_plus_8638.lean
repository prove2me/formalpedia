-- Prove2me | solution 1 for lean_workbook_plus_8638
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:06.758569+00:00
-- url     : https://prove2.me/submissions/6edd2ba0-47c3-4e37-ba3d-77aa3af9bb27

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (p : ℕ) (h : p.Prime) (h5 : p ≥ 5) : 4 ∣ p + 1 ∨ 4 ∣ p - 1 := by
  have ho : p % 2 = 1 := h.eq_two_or_odd.resolve_left (by omega)
  simp only [Nat.dvd_iff_mod_eq_zero]
  omega
