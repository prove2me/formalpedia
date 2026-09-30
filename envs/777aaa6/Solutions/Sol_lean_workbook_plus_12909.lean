-- Prove2me | solution 1 for lean_workbook_plus_12909
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:42.511147+00:00
-- url     : https://prove2.me/submissions/fe2e4a75-be10-4abc-9b8e-735facedc30d

import Mathlib.Analysis.Complex.Basic

theorem solution (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : q ∣ q^2 + 1) (h' : p ∣ q^2 - 1) : ¬(Nat.Prime (p + q + 1)) := by
  exfalso
  have hq2 : q ∣ q^2 := dvd_pow_self q two_ne_zero
  have h1 : q ∣ 1 := (Nat.dvd_add_right hq2).mp h
  have := Nat.le_of_dvd one_pos h1
  have := hq.two_le
  omega
