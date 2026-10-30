-- Prove2me | Theorems.Thm_gpy_tupleProdCount_two_submul
-- name    : gpy_tupleProdCount_two_submul
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:27:34.31787+00:00
-- url     : https://prove2.me/theorems/1f7d1be2-7de5-477d-aa08-a04a90265996
-- title:
--   The 2-fold divisor count is submultiplicative
-- statement:
--   For any d and m, the number of ordered factorizations of d times m into two positive factors is at most the product of the corresponding counts for d and for m, by the gcd-splitting injection. Formalization Note: the divisor counts are written out in Mathlib terms as cardinalities of filtered tuple sets, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_tupleProdCount_two_submul {d m : ℕ} :
    ((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d * m))).filter (fun t => ∏ i, t i = (d * m))).card ≤ ((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d))).filter (fun t => ∏ i, t i = (d))).card * ((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (m))).filter (fun t => ∏ i, t i = (m))).card := by sorry
