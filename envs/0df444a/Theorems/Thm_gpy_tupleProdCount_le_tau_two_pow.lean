-- Prove2me | Theorems.Thm_gpy_tupleProdCount_le_tau_two_pow
-- name    : gpy_tupleProdCount_le_tau_two_pow
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:30:43.450137+00:00
-- url     : https://prove2.me/theorems/f3899ee2-7170-449d-8f96-ace0605ceae3
-- title:
--   The (k+1)-fold divisor count is at most the k-th power of the 2-fold count
-- statement:
--   For L at least 1 and any k, the number of ordered factorizations of L into k+1 positive factors is at most the k-th power of the number of ordered factorizations of L into two positive factors, by induction on k using the convolution identity and monotonicity under divisibility. Formalization Note: the divisor counts are written out in Mathlib terms as cardinalities of filtered tuple sets, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_tupleProdCount_le_tau_two_pow (k : ℕ) {L : ℕ} (hL : 1 ≤ L) :
    ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card ≤ (((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card) ^ k := by sorry
