-- Prove2me | Theorems.Thm_ZMod_not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one
-- name    : ZMod.not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/add42515-774b-5704-8a9b-4047e4c3f560
-- title:
--   No root of x²+x+1 modulo M
-- statement:
--   Let $M$ be a natural number such that $3 \nmid M$, and suppose there exists a natural number $\ell$ which is prime, divides $M$, and satisfies $\ell \bmod 3 \neq 1$. Then there is no element $x$ of $\mathbb{Z}/M\mathbb{Z}$ with $x^2 + x + 1 = 0$. Note that $M$ is unrestricted: for $M = 0$ the ring is $\mathbb{Z}$ and the hypotheses are satisfied by any prime $\ell \not\equiv 1 \pmod 3$, while for $M = 1$ the existence hypothesis fails, so the statement is vacuous there. The prime $\ell$ is allowed to be $2$, since $2 \bmod 3 = 2 \neq 1$; only congruence to $1$ modulo $3$ is excluded, the divisor $3$ itself being ruled out separately by $3 \nmid M$. In other words, the congruence $x^2 + x + 1 \equiv 0 \pmod M$ is insoluble as soon as $M$ is not divisible by $3$ and has at least one prime divisor that is not $\equiv 1 \pmod 3$.
--
--   This is the elementary criterion for the absence of a primitive cube root of unity in $\mathbb{Z}/M\mathbb{Z}$, resting on the classical fact that a prime $\ell \neq 3$ has $-3$ as a quadratic residue exactly when $\ell \equiv 1 \pmod 3$. It is used in the analysis of inertia at the relevant points of the integral model of $X_1(N)/X_0(N)$-type modular curves, where a cyclic inertia group of order prime to the residue characteristic is produced in the case $\ell = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ZMod_not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ZMod.not_exists_sq_add_self_add_one_eq_zero_of_not_three_dvd_of_exists_prime_dvd_mod_three_ne_one
    (M : ℕ) (hM : ¬ 3 ∣ M) (hℓ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ M ∧ ℓ % 3 ≠ 1) :
    ¬ ∃ x : ZMod M, x ^ 2 + x + 1 = 0 := by sorry
