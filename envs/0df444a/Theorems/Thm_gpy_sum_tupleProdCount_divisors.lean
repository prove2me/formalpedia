-- Prove2me | Theorems.Thm_gpy_sum_tupleProdCount_divisors
-- name    : gpy_sum_tupleProdCount_divisors
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T20:25:56.895848+00:00
-- url     : https://prove2.me/theorems/7d9ae3a5-24d6-4fc9-9a52-47111b52ee90
-- title:
--   Summing tau_k over divisors gives tau_{k+1}
-- statement:
--   Summing the k-fold divisor function tau_k(D) over the divisors D of L gives tau_{k+1}(L), via the convolution identity for tau and the divisor involution D ↦ L / D.
-- source:
--   GPY Selberg fiber bound for tuple weights, formalized from Mathlib (squarefree products, pairwise coprimality, and fiber counting)

import Mathlib
open Classical

theorem gpy_sum_tupleProdCount_divisors {k L : ℕ} (hL : L ≠ 0) :
    ∑ D ∈ L.divisors,
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
          (fun d => ∏ i, d i = D)).card
      = ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card := by sorry
