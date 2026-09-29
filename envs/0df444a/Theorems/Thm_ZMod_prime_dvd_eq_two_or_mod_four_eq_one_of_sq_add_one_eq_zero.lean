-- Prove2me | Theorems.Thm_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero
-- name    : ZMod.prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/7763b8bc-4814-53a8-a56e-60f31f15536f
-- title:
--   Prime divisors of M admitting a square root of -1
-- statement:
--   Let $M$ be a natural number and let $x$ be an element of $\mathbb{Z}/M\mathbb{Z}$ with $x^2 + 1 = 0$. Let $\ell$ be a prime number dividing $M$. Then $\ell = 2$ or $\ell \equiv 1 \pmod 4$, i.e. $\ell \bmod 4 = 1$ as natural numbers. Equivalently: if the congruence $x^2 \equiv -1 \pmod M$ is solvable, then no prime divisor of $M$ is congruent to $3$ modulo $4$. Note that the case $M = 0$ is permitted by the statement, where $\mathbb{Z}/M\mathbb{Z}$ is $\mathbb{Z}$ and every prime divides $M$; in that case the hypothesis $x^2 + 1 = 0$ is vacuously unsatisfiable, so the assertion holds. The conclusion is a disjunction of natural-number statements about $\ell$ alone; nothing is asserted about the residue of $M$ itself (indeed $4 \mid M$ is excluded only indirectly, via the absence of a prime $\ell \equiv 3 \pmod 4$ being insufficient, so the statement as given genuinely allows $\ell = 2$).
--
--   This is the first supplement to quadratic reciprocity in the form used for the solvability of $x^2 \equiv -1 \pmod M$: $-1$ is a square modulo an odd prime exactly when that prime is $1$ modulo $4$. It feeds the derivation that no square root of $-1$ exists modulo an odd $M$ having a prime divisor congruent to $3$ modulo $4$, recorded in [`ZMod.not_exists_sq_add_one_eq_zero_of_not_two_dvd_of_exists_prime_dvd_mod_four_ne_one`](thm.html#ZMod.not_exists_sq_add_one_eq_zero_of_not_two_dvd_of_exists_prime_dvd_mod_four_ne_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ZMod.prime_dvd_eq_two_or_mod_four_eq_one_of_sq_add_one_eq_zero
    {M : ℕ} (x : ZMod M) (hx : x ^ 2 + 1 = 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) :
    ℓ = 2 ∨ ℓ % 4 = 1 := by sorry
