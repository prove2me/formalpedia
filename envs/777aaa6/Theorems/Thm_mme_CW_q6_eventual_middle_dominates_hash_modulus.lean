-- Prove2me | Theorems.Thm_mme_CW_q6_eventual_middle_dominates_hash_modulus
-- name    : mme_CW_q6_eventual_middle_dominates_hash_modulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:26:44.072262+00:00
-- url     : https://prove2.me/theorems/a2a6ac8e-9a9e-4cd2-bf9b-07b1b3425964
-- title:
--   The CW q=6 profile eventually separates the middle binomial count from the hash modulus
-- statement:
--   Let (L_N,G_N) be arbitrary sequences of nonnegative integers. Uniformly for all sufficiently large (N), if (L_N+G_N=N) and (341L_N<100G_N), then, writing (X_N=\binom{N}{G_N}) and (B_N=\binom{2G_N}{G_N}), one has $$400(4X_N^2+1)\le B_N.$$ This is the exact eventually-large comparison needed to choose the q=6 affine-hash concentration and collision thresholds. The strict profile ratio supplies a uniform exponential gap; the factor 400 absorbs every fixed and polynomial loss.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–272: the q=6 profile condition and affine-hash modulus M=4*choose(N,G)^2+1; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

open BigOperators Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_eventual_middle_dominates_hash_modulus
    (L G : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      (L N + G N = N ∧ 341 * L N < 100 * G N) →
        400 * (4 * (Nat.choose N (G N)) ^ 2 + 1) ≤
          Nat.choose (2 * G N) (G N) := by
  sorry
