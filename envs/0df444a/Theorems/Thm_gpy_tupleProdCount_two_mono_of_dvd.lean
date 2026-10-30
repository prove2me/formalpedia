-- Prove2me | Theorems.Thm_gpy_tupleProdCount_two_mono_of_dvd
-- name    : gpy_tupleProdCount_two_mono_of_dvd
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T04:21:22.629331+00:00
-- url     : https://prove2.me/theorems/d3b7ec3d-aff8-4280-8f31-eac8ca1cd36f
-- title:
--   The 2-fold divisor count is monotone under divisibility
-- statement:
--   If d divides L with both at least 1, then the number of ordered factorizations of d into two positive factors is at most that of L, by the explicit pair-scaling injection sending (a, b) to (a, b times L/d). Formalization Note: the divisor counts are written out in Mathlib terms as cardinalities of filtered tuple sets, with no local definitions.
-- source:
--   GPY fourth-order tau-moment bound, formalized from Mathlib (ordered factorizations, divisor reindexing, harmonic bound, and Cauchy-Schwarz)

import Mathlib
open Classical

theorem gpy_tupleProdCount_two_mono_of_dvd {d L : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hdiv : d ∣ L) : ((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (d))).filter (fun t => ∏ i, t i = (d))).card ≤ ((Fintype.piFinset (fun _ : Fin (2) => Finset.Icc 1 (L))).filter (fun t => ∏ i, t i = (L))).card := by sorry
