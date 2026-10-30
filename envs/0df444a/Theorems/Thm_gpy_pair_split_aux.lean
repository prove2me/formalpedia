-- Prove2me | Theorems.Thm_gpy_pair_split_aux
-- name    : gpy_pair_split_aux
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:24:30.516164+00:00
-- url     : https://prove2.me/theorems/c59ff488-c596-4259-bfb7-18d6785cb7ca
-- title:
--   Gcd-splitting of a factorization
-- statement:
--   If a times b equals d times m with d and m at least 1 and a at least 1, then writing g for the gcd of a and d, a2 for a/g, d1 for d/g, and m2 for m/a2 splits the factorization into one of d and one of m, with all the stated positivity and size bounds. This is the arithmetic core of the submultiplicativity of the 2-fold divisor count. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_pair_split_aux {a b d m g a2 d1 m2 : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) (h : a * b = d * m) (ha : 1 ≤ a)
    (hg : g = Nat.gcd a d) (ha2 : a2 = a / g) (hd1 : d1 = d / g)
    (hm2 : m2 = m / a2) :
    g * a2 = a ∧ g * d1 = d ∧ a2 * m2 = m ∧ d1 * m2 = b ∧
    1 ≤ g ∧ g ≤ d ∧ 1 ≤ d1 ∧ d1 ≤ d ∧ 1 ≤ a2 ∧ a2 ≤ m ∧
    1 ≤ m2 ∧ m2 ≤ m := by sorry
