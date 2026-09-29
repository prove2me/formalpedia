-- Prove2me | Theorems.Thm_cyclotomic_velu_powerSums
-- name    : cyclotomic_velu_powerSums
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/20c7dee3-4db9-5023-89b7-a5f1c5599f53
-- title:
--   Power sums of ζ^k/(1-ζ^k)² over half the p-th roots
-- statement:
--   Let $F$ be a field of characteristic zero, let $p$ be a prime with $p \neq 2$, and let $\zeta \in F$ be a primitive $p$-th root of unity. Writing $x_k = \zeta^k/(1-\zeta^k)^2$ for $k$ in the integer interval $[1, p/2]$ (natural-number division, so $k$ runs over $1 \le k \le (p-1)/2$), the theorem asserts the conjunction of three identities in $F$, with $p$ read as an element of $F$ via the canonical map from $\mathbb{N}$: first, $\sum_k x_k = -(p^2-1)/24$; second, $\sum_k x_k^2 = (p^2-1)(p^2+11)/1440$; and third, $\sum_k x_k^3 = -\bigl((p^2-1)(2p^4 + 23p^2 + 191)\bigr)/120960$. The divisions by $24$, $1440$ and $120960$ make sense because $F$ has characteristic zero. The hypotheses that $p$ is prime and odd enter both through the primitivity of $\zeta$ (so that no denominator $1-\zeta^k$ vanishes for $1 \le k \le (p-1)/2$) and through the pairing $k \leftrightarrow p-k$, under which $x_k$ is invariant.
--
--   These are the first three power sums, obtained from Newton's identities applied to the roots of $y^p - (y-1)^p$, of the abscissae of the half-kernel of $\mu_p$ on the split nodal cubic $y^2 + xy = x^3$; they are precisely the quantities consumed by Vélu's isogeny formulae, and in particular determine $c_4$ and $c_6$ of the quotient node. They feed the toric branch of the zero-component transport law, being cited by [`WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative`](thm.html#WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative) and by [`WeierstrassCurve.valuation_c4_add_veluTSum_lt_one_of_formal_kernel`](thm.html#WeierstrassCurve.valuation_c4_add_veluTSum_lt_one_of_formal_kernel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_cyclotomic_velu_powerSums.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem cyclotomic_velu_powerSums {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p) :
    (∑ k ∈ Finset.Icc 1 (p / 2), ζ ^ k / (1 - ζ ^ k) ^ 2 = -((p : F) ^ 2 - 1) / 24) ∧
    (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2
        = ((p : F) ^ 2 - 1) * ((p : F) ^ 2 + 11) / 1440) ∧
    (∑ k ∈ Finset.Icc 1 (p / 2), (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 3
        = -(((p : F) ^ 2 - 1) * (2 * (p : F) ^ 4 + 23 * (p : F) ^ 2 + 191)) / 120960) := by sorry
