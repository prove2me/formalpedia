-- Prove2me | Theorems.Thm_mme_CW_q6_primary_capacity_factorial_identity
-- name    : mme_CW_q6_primary_capacity_factorial_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:01:58.742796+00:00
-- url     : https://prove2.me/theorems/d60e635f-37e2-4ae0-a8a3-a636f84d739f
-- title:
--   Exact factorial form of the coupled q=6 finite capacity
-- statement:
--   Let $L+G=N$, and put
--
--   $$
--   Z=\binom{2N}{L}\binom{2N-L}{L},\qquad X=\binom NG,\qquad B=\binom{2G}{G}.
--   $$
--
--   Then the finite coupled $q=6$ capacity has the exact factorial expression
--
--   $$
--   \frac{Z^3B^2}{16X^4}=\frac{((2N)!)^3}{16(L!)^2(2G)!(N!)^4}.
--   $$
--
--   This cancellation isolates the single factorial quotient whose Stirling estimate supplies the analytic capacity term in the primary Coppersmith--Winograd extraction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), multinomial quantities in the C-tensor estimate on journal pp. 270--272; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib

theorem mme_CW_q6_primary_capacity_factorial_identity
    (N L G : ℕ) (hLG : L + G = N) :
    let Z := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
    let X := Nat.choose N G
    let B := Nat.choose (2 * G) G
    (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) /
        (16 * (X : ℝ) ^ 4)) =
      (((2 * N).factorial : ℝ) ^ 3 /
        (16 * (L.factorial : ℝ) ^ 2 *
          ((2 * G).factorial : ℝ) * (N.factorial : ℝ) ^ 4)) := by
  sorry
