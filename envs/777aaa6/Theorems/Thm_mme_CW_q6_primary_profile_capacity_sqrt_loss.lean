-- Prove2me | Theorems.Thm_mme_CW_q6_primary_profile_capacity_sqrt_loss
-- name    : mme_CW_q6_primary_profile_capacity_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:25:08.503222+00:00
-- url     : https://prove2.me/theorems/0cec3e50-a5d8-4c98-83ad-440a9dfec495
-- title:
--   Coupled q=6 optimal floor profile: multinomial capacity with square-root loss
-- statement:
--   Let $3\tau\ge2$, and let positive integers $L,G$ sum to $N$. Assume $L$ is the lower integer rounding of the optimizing proportion $2N/(6^{3\tau}+2)$, in the precise sense that it lies between that real number minus one and the number itself. Write
--
--   $$
--   Z=\binom{2N}{L}\binom{2N-L}{L},\qquad X=\binom NG,\qquad B=\binom{2G}{G},
--   $$
--
--   $$
--   \mathcal C_{N,L,G}=\frac{Z^3B^2}{16X^4},\qquad S_{L,G}=36^{2G}6^{2L}.
--   $$
--
--   There is an absolute square-root-loss constant $C\ge0$ such that
--
--   $$
--   \left(4\,6^{3\tau}(6^{3\tau}+2)\right)^{2N}e^{-C\sqrt{N+1}}\le \mathcal C_{N,L,G}(S_{L,G}^3)^\tau.
--   $$
--
--   This is the deterministic profile-rate half of the coupled Coppersmith--Winograd calculation. It keeps the exact binomial capacity and exact floor rounding, and absorbs only the polynomial Stirling discrepancy into $e^{-O(\sqrt N)}$; hashing and tensor realization are deliberately separate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 266-271, specialized to q=6; the exact profile is also the coupled 121/211 value used in Duan--Wu--Zhou, arXiv:2210.10173v5, Section 6.3.

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

open Filter Topology

set_option autoImplicit false

theorem mme_CW_q6_primary_profile_capacity_sqrt_loss
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N L G : ℕ), 2 ≤ N → 0 < L → 0 < G → L + G = N →
        (L : ℝ) ≤
            (2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ) →
        (2 / ((6 : ℝ) ^ (3 * tau) + 2)) * (N : ℝ) <
            (L : ℝ) + 1 →
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        let Z : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let X : ℕ := Nat.choose N G
        let B : ℕ := Nat.choose (2 * G) G
        let capacity : ℝ :=
          ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
        raw ^ (2 * N) *
            Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          capacity * ((((side * side * side : ℕ) : ℝ)) ^ tau) := by sorry
