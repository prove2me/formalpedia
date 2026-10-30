-- Prove2me | Theorems.Thm_gpy_sum_divisors_sum_reindex
-- name    : gpy_sum_divisors_sum_reindex
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:32:48.53078+00:00
-- url     : https://prove2.me/theorems/9688a2e5-b0a3-4bd6-a0e6-a9cdcda047b7
-- title:
--   Divisor reindexing for a summand depending on D
-- statement:
--   Summing G(D) over e dividing D and D between 1 and R is the same as summing G(e times m) over m between 1 and R/e and e between 1 and R. This is a variant of the divisor reindexing for a summand depending on D itself. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_sum_divisors_sum_reindex (G : ℕ → ℝ) (R : ℕ) :
    ∑ D ∈ Finset.Icc 1 R, ∑ e ∈ Nat.divisors D, G D
      = ∑ e ∈ Finset.Icc 1 R, ∑ m ∈ Finset.Icc 1 (R / e), G (e * m) := by sorry
