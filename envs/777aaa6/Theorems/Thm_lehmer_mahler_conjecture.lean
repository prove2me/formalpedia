-- Prove2me | Theorems.Thm_lehmer_mahler_conjecture
-- name    : lehmer_mahler_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T19:58:12.351554+00:00
-- url     : https://prove2.me/theorems/c1ef4cc2-f921-4b19-9a7b-f13b15f1910b
-- statement:
--   Lehmer's conjecture (1933): The Mahler measure of any non-cyclotomic irreducible polynomial over ℤ is at least Lehmer's number ≈ 1.17628. This would bound the smallest algebraic integers in terms of their degree.
-- source:
--   https://en.wikipedia.org/wiki/Lehmer%27s_conjecture

import Mathlib

import Mathlib

-- Lehmer's conjecture: the Mahler measure of a non-cyclotomic irreducible polynomial
-- over ℤ is at least Lehmer's number ≈ 1.1762808...
-- (the Mahler measure of x^10 + x^9 - x^7 - x^6 - x^5 - x^4 - x^3 + x + 1)
-- Formalized: if p : Polynomial ℤ is irreducible, monic, non-cyclotomic, then M(p) ≥ c
theorem lehmer_mahler_conjecture :
    ∃ c : ℝ, 1 < c ∧
    ∀ p : Polynomial ℤ, Irreducible p → p.Monic →
      (¬∃ n : ℕ, 1 ≤ n ∧ p ∣ (Polynomial.cyclotomic n ℤ)) →
      c ≤ (Finset.univ.prod (fun z : p.roots.toFinset =>
        max 1 (Complex.normSq z))) := by
  sorry
