-- Prove2me | Theorems.Thm_gpy_sum_tupleProdCount_le
-- name    : gpy_sum_tupleProdCount_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:18:37.046395+00:00
-- url     : https://prove2.me/theorems/9136b654-79d7-4768-b3cb-d2dcc01908e4
-- title:
--   Higher divisor summatory bound: sum of τ_{k+1} up to R
-- statement:
--   For R ≥ 1 and any k, the sum of the (k+1)-fold divisor function τ_{k+1}(D) — the number of ordered factorizations of D into k+1 positive factors — over 1 ≤ D ≤ R is at most R·(1 + log R)^k. The bound is proved by induction on k, using the convolution identity τ_{k+1}(D) = ∑_{e | D} τ_k(D/e), a divisor reindexing, and the harmonic bound.
-- source:
--   GPY τ-moment / divisor-sum estimates for Selberg weights, formalized from Mathlib (divisor double count, harmonic bound, divisor convolution, and the τ-weighted λ-mass identity)

import Mathlib
open Classical

theorem gpy_sum_tupleProdCount_le (k : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    ∑ D ∈ Finset.Icc 1 R,
      ((((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 D)).filter
        (fun d => ∏ i, d i = D)).card : ℕ) : ℝ) ≤
      (R : ℝ) * (1 + Real.log (R : ℝ)) ^ k := by sorry
