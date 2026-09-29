-- Prove2me | Theorems.Thm_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
-- name    : eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f9e9121d-7d65-5c0a-abc5-b7424d21cd39
-- title:
--   Vanishing second differences force an affine sequence
-- statement:
--   Let $R$ be a commutative ring, let $e$ be a natural number, and let $a \colon \mathbb{N} \to R$ be a sequence. Assume that the second differences of $a$ vanish in the range determined by $e$, namely that $a_k - 2a_{k+1} + a_{k+2} = 0$ for every natural number $k$ with $k + 1 < e$; note that this hypothesis is vacuous when $e \le 1$. Then for every natural number $k$ with $k \le e$ one has
--   $$a_k = a_0 + (a_1 - a_0)\cdot k,$$
--   where $k$ is understood via the canonical ring homomorphism $\mathbb{N} \to R$. Thus on the initial segment $\{0, 1, \dots, e\}$ the sequence is the arithmetic progression with initial term $a_0$ and common difference $a_1 - a_0$. The recurrence is stated in the shifted form with indices $k$, $k+1$, $k+2$ rather than $k-1$, $k$, $k+1$, so that no truncated subtraction on $\mathbb{N}$ occurs; the conclusion is asserted for all indices up to and including $e$, one step beyond the last index at which the recurrence is assumed.
--
--   This is the elementary statement that solutions of the linear recurrence $a_{k+2} = 2a_{k+1} - a_k$, whose characteristic polynomial is $(x-1)^2$, are exactly the affine sequences — equivalently, that a discrete harmonic function on a path is affine. It is used in the analysis of divisors supported on the special fibre of a resolution of an $A_{e-1}$ singularity, where the condition of zero intersection with each exceptional component is precisely the vanishing of second differences; the consumer is [`MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero`](thm.html#MvPolynomial.CrossingQuotient.Resolution.exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem eq_add_sub_mul_natCast_of_sub_two_mul_add_eq_zero
    {R : Type*} [CommRing R] (e : ℕ) (a : ℕ → R)
    (h : ∀ k : ℕ, k + 1 < e → a k - 2 * a (k + 1) + a (k + 2) = 0)
    (k : ℕ) (hk : k ≤ e) :
    a k = a 0 + (a 1 - a 0) * k := by sorry
