-- Prove2me | solution 1 for lean_workbook_plus_52892
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:31.31826+00:00
-- url     : https://prove2.me/submissions/e9540e16-e6dd-4191-8b7e-6c4f0ee1ae9b

import Mathlib.Analysis.Complex.Basic

theorem solution (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : q ∣ q^2 + 1) (h' : p ∣ q^2 - 1) : ¬(p + q + 1).Prime := by
  exfalso
  have h1 : q ∣ q ^ 2 := dvd_pow_self q two_ne_zero
  have h2 : q ∣ 1 := (Nat.dvd_add_right h1).mp h
  have h3 : q = 1 := Nat.dvd_one.mp h2
  exact hq.one_lt.ne' h3
