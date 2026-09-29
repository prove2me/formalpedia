-- Prove2me | Theorems.Thm_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero
-- name    : ZMod.prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/d9db5ff3-deff-5ba4-bac9-d1e69d4b6047
-- title:
--   Prime divisors of M when x²+x+1≡ 0 (mod M)
-- statement:
--   Let $M$ be a natural number and let $x$ be an element of $\mathbb{Z}/M\mathbb{Z}$ satisfying $x^2 + x + 1 = 0$. Let $\ell$ be a prime number dividing $M$. Then either $\ell = 3$ or $\ell \equiv 1 \pmod 3$, in the sense that the natural-number remainder $\ell \bmod 3$ equals $1$. Note that $M$ is an arbitrary natural number, so the degenerate cases $M = 0$ and $M = 1$ are included; the divisibility hypothesis $\ell \mid M$ is what supplies the reduction map $\mathbb{Z}/M\mathbb{Z} \to \mathbb{Z}/\ell\mathbb{Z}$, and the conclusion is a statement about the residue of $\ell$ modulo $3$ only.
--
--   This is the elementary determination of the primes modulo which the cyclotomic polynomial $X^2 + X + 1$ has a root: the splitting primes are exactly $3$ and those congruent to $1$ modulo $3$. It is used to rule out roots of $X^2+X+1$ modulo $M$ when $M$ has a prime divisor that is neither $3$ nor $1$ mod $3$, as recorded by [`ZMod.not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one`](thm.html#ZMod.not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ZMod.prime_dvd_eq_three_or_mod_three_eq_one_of_sq_add_self_add_one_eq_zero
    {M : ℕ} (x : ZMod M) (hx : x ^ 2 + x + 1 = 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) :
    ℓ = 3 ∨ ℓ % 3 = 1 := by sorry
