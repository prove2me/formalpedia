-- Prove2me | Theorems.Thm_add_two_mul_pow_two_pow_eq
-- name    : add_two_mul_pow_two_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/405e323a-552b-5a32-a63a-f92b49c60a72
-- title:
--   Binomial expansion of (u+2v)^{2^n} modulo 2ⁿ⁺²
-- statement:
--   Let $A$ be a commutative ring, let $n$ be a natural number with $1 \le n$, and let $u, v \in A$. The assertion is that there exists $w \in A$ with
--   $$(u + 2v)^{2^n} = u^{2^n} + 2^{\,n+1}\bigl(u^{2^n-1}v + u^{2^n-2}v^2\bigr) + 2^{\,n+2}\,w,$$
--   where the exponents $2^n-1$ and $2^n-2$ are truncated natural-number differences (harmless, since $n \ge 1$ gives $2^n \ge 2$) and the integers $2$, $2^{n+1}$, $2^{n+2}$ act through the canonical ring map $\mathbb{Z} \to A$. Equivalently: modulo $2^{n+2}A$ the $2^n$-th power of $u + 2v$ agrees with $u^{2^n}$ plus the two displayed terms of weight $2^{n+1}$, one linear and one quadratic in $v$. No hypothesis beyond commutativity of $A$ and $n \ge 1$ is imposed; in particular $A$ need not be of characteristic $2$, nor $2$-adically complete, nor free of $2$-torsion.
--
--   This is the exceptional case $p = 2$, $r = 1$ of the elementary binomial estimate for $p$-th power maps: for odd $p$ all terms past the linear one are divisible by $p^{n+2}$, whereas at $p=2$ the quadratic binomial coefficient $\binom{2^n}{2}(2v)^2 = 2^{n+1}(2^n-1)u^{2^n-2}v^2$ is divisible only by $2^{n+1}$ and survives modulo $2^{n+2}$. It is used in the local deformation-theoretic computations, by [`Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two`](thm.html#Deformation.PLoc.wPartialSum_adicEval_add_sub_sub_algebraMap_mul_add_mem_powSub_two), where the surviving square term forces the normal form of the $w$-series at $p = 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_add_two_mul_pow_two_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem add_two_mul_pow_two_pow_eq
    {A : Type u} [CommRing A] (n : ℕ) (hn : 1 ≤ n) (u v : A) :
    ∃ w : A, (u + 2 * v) ^ (2 ^ n) =
      u ^ (2 ^ n) + 2 ^ (n + 1) * (u ^ (2 ^ n - 1) * v + u ^ (2 ^ n - 2) * v ^ 2) + 2 ^ (n + 2) * w := by sorry
