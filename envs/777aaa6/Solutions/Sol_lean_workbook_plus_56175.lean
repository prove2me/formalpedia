-- Prove2me | solution 1 for lean_workbook_plus_56175
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:11.670537+00:00
-- url     : https://prove2.me/submissions/153247a1-e888-4baf-a00f-1522e6b8471f

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℕ) (h1 : 1 < x ∧ 1 < y ∧ 1 < z) (h2 : Nat.gcd x y = 1) (h3 : x^3*y^2 + y^3*x^2 + (x*y)^2 = z^3) : ∃ x y z : ℕ, (1 < x ∧ 1 < y ∧ 1 < z ∧ Nat.gcd x y = 1 ∧ x^3*y^2 + y^3*x^2 + (x*y)^2 = z^3) :=
  ⟨x, y, z, h1.1, h1.2.1, h1.2.2, h2, h3⟩
