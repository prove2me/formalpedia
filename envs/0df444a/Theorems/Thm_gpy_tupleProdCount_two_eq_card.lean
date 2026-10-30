-- Prove2me | Theorems.Thm_gpy_tupleProdCount_two_eq_card
-- name    : gpy_tupleProdCount_two_eq_card
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:18:16.362792+00:00
-- url     : https://prove2.me/theorems/80d90e05-0fd8-49c4-bcc0-532a45ebebdd
-- title:
--   The 2-fold divisor count is the divisor count
-- statement:
--   For D at least 1, the number of ordered factorizations of D into two positive factors equals the number of divisors of D. Formalization Note: the 2-fold divisor count is written out in Mathlib terms as the cardinality of the filtered tuple set, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_tupleProdCount_two_eq_card {D : ℕ} (hD : 1 ≤ D) :
    ((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (D))).filter (fun t => ∏ i, t i = (D))).card = (Nat.divisors D).card := by sorry
