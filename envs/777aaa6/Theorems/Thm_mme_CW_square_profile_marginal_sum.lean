-- Prove2me | Theorems.Thm_mme_CW_square_profile_marginal_sum
-- name    : mme_CW_square_profile_marginal_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:45:36.427715+00:00
-- url     : https://prove2.me/theorems/e50e79e9-dea0-4da3-9f57-8fe1d023fb9b
-- title:
--   The five CW square-profile marginals sum to the profile length
-- statement:
--   Let $A,B,C,D$ be the integer multiplicities assigned respectively to the cyclic constituent shapes $(0,0,4)$, $(0,1,3)$, $(0,2,2)$, and $(1,1,2)$ in a length-$N$ tensor-square profile. If $3A+6B+3C+3D=N$, then the five marginal counts from equation (13),
--
--   $$
--   2A+2B+C,\quad 2B+2D,\quad 2C+D,\quad 2B,\quad A,
--   $$
--
--   sum to $N$. This is the exact integer compatibility condition needed for the five marginal multinomial coefficients in the pruning count.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equation (13) on journal p. 268 (PDF p. 18); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Tactic

theorem mme_CW_square_profile_marginal_sum
    (A B C D N : ℕ)
    (hnorm : 3 * A + 6 * B + 3 * C + 3 * D = N) :
    (2 * A + 2 * B + C) + (2 * B + 2 * D) +
        (2 * C + D) + 2 * B + A = N := by sorry
