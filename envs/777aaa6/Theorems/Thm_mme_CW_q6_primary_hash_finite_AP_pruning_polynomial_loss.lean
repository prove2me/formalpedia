-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
-- name    : mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:25:59.547859+00:00
-- url     : https://prove2.me/theorems/8b7c6ccb-69c7-486f-9bce-49cdf0efff7d
-- title:
--   Finite progression-free pruning of the regular coupled q=6 profile
-- statement:
--   There is a universal positive integer $d$ with the following property. Let the exact coupled $q=6$ profile incidence hypergraph at parameters $(N,L,G)$ have the CW90 regularity counts, where $L>0$, $L+G=N$, and $341L<100G$. Write
--
--   $$
--   Z=\binom{2N}{L}\binom{2N-L}{L},\qquad X=\binom NG,\qquad B=\binom{2G}{G},\qquad M=4X^2+1.
--   $$
--
--   For every nonempty three-term-progression-free set $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$, finite modular hashing, collision pruning, and uniform degree bucketing produce an induced primary hash family with $A$ outer fibers of common positive size $H$, satisfying
--
--   $$
--   H\le 4^N,\qquad
--   Z\,\frac{(|S|/M)^d}{(N+1)^d}\le A,\qquad
--   B\,\frac{(|S|/M)^d}{(N+1)^d}\le 4X^2H.
--   $$
--
--   The lower-half condition is the finite no-wrap interface between ordinary three-term-progression freeness and the odd modulus $M$. The unspecified universal power $d$ records only a fixed number of density factors and polynomial losses; the theorem makes no tensor-realization or common fine-coordinate claim.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–271: exact regular degrees, the odd modulus M=4*choose(N,G)^2+1, Salem–Spencer hashing, deletion of repeated X/Y blocks, and extraction of common-H C-tensor fibers; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_q6_exact_address_incidence
import Theorems.Thm_mme_3AP_free_no_collision

open MME

theorem mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ A H : ℕ,
            ∃ family : CWQ6PrimaryHashFamily N L G A H,
              H ≤ 4 ^ N ∧
              (Zcount : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                (A : ℝ) ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
