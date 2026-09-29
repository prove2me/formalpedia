-- Prove2me | Theorems.Thm_cyclotomic_velu_xLaw
-- name    : cyclotomic_velu_xLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c3c6944c-4f32-51f4-a8d3-e74c29aec63f
-- title:
--   Vélu's x-map for μₚ on the split node
-- statement:
--   Let $F$ be a field of characteristic zero, let $p$ be a prime with $p \neq 2$, and let $\zeta \in F$ be a primitive $p$-th root of unity. Write $x_k = \zeta^k/(1-\zeta^k)^2$ for $k$ in the integer interval $[1, \lfloor p/2 \rfloor]$ (natural-number division, so $\lfloor p/2\rfloor = (p-1)/2$ as $p$ is odd). Let $X \in F$ satisfy $X \neq x_k$ for every such $k$. Then
--   $$X + \sum_{k=1}^{\lfloor p/2\rfloor}\left(\frac{x_k\,(1 + 6x_k)}{X - x_k} + \frac{x_k^2\,(1 + 4x_k)}{(X - x_k)^2}\right) - \frac{p^2 - 1}{12} \;=\; \frac{X^p}{\prod_{k=1}^{\lfloor p/2\rfloor} (X - x_k)^2},$$
--   where $p^2-1$ and $12$ are read in $F$ (legitimate since $\operatorname{char} F = 0$). The hypothesis $X \neq x_k$ is exactly what makes both sides defined; all terms are elements of $F$, so the assertion is a pointwise identity at every admissible $X$, equivalent to the corresponding identity of rational functions in $X$.
--
--   This is the explicit form of Vélu's $x$-coordinate map for the quotient of the standard split nodal cubic $y^2 + xy = x^3$, whose smooth points carry the multiplicative group structure with the point of parameter $\zeta^k$ having abscissa $\zeta^k/(1-\zeta^k)^2$, by the subgroup $\mu_p$: the resulting rational function is the $p$-th power map, up to the additive normalising constant $(p^2-1)/12$. It is used in [`WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative`](thm.html#WeierstrassCurve.inZeroComponentAt_veluCoord_iff_of_multiplicative) to evaluate Vélu's $x$-map at a multiplicative place, giving the toric branch of the transport law for the zero component under a Vélu quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_cyclotomic_velu_xLaw.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve

theorem cyclotomic_velu_xLaw {F : Type*} [Field F] [CharZero F]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (X : F) (hX : ∀ k ∈ Finset.Icc 1 (p / 2), X ≠ ζ ^ k / (1 - ζ ^ k) ^ 2) :
    X + ∑ k ∈ Finset.Icc 1 (p / 2),
        (ζ ^ k / (1 - ζ ^ k) ^ 2 * (1 + 6 * (ζ ^ k / (1 - ζ ^ k) ^ 2)) / (X - ζ ^ k / (1 - ζ ^ k) ^ 2)
          + (ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 * (1 + 4 * (ζ ^ k / (1 - ζ ^ k) ^ 2))
              / (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2)
      - ((p : F) ^ 2 - 1) / 12
      = X ^ p / ∏ k ∈ Finset.Icc 1 (p / 2), (X - ζ ^ k / (1 - ζ ^ k) ^ 2) ^ 2 := by sorry
