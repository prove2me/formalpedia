-- Prove2me | Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
-- name    : ringKrullDim_le_of_ringHom_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/984d557f-0ff9-50a6-8bec-45c3148a7a96
-- title:
--   Krull dimension does not increase along an integral homomorphism
-- statement:
--   Let $R$ and $S$ be commutative rings (in arbitrary universes), and let $\varphi \colon R \to S$ be a ring homomorphism which is integral in the sense of `RingHom.IsIntegral`: every element of $S$ satisfies a monic polynomial whose coefficients lie in the image of $\varphi$, i.e. $S$ is an integral algebra over $R$ for the algebra structure induced by $\varphi$. The conclusion is the inequality $\dim S \le \dim R$ between the Krull dimensions in the sense of `ringKrullDim`, that is, between the order-theoretic Krull dimensions of the prime spectra, taken as values in $\mathbb{Z} \cup \{\pm\infty\}$ (so the case of the zero ring, whose dimension is $\bot$, is covered). No injectivity, flatness or finiteness hypothesis beyond integrality is imposed, and no converse inequality is asserted: the statement is the one-sided bound only, whereas for an injective integral homomorphism the two dimensions in fact agree.
--
--   This is the dimension inequality coming from the Cohen–Seidenberg incomparability theorem: distinct comparable primes of $S$ contract to distinct primes of $R$, so chains in $\operatorname{Spec} S$ transport to chains of the same length in $\operatorname{Spec} R$. It is used in the study of two-chart integral models of algebraic curves, where it bounds the Krull dimension of stalks and of quotients by germ ideals in terms of the dimension of the base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ringKrullDim_le_of_ringHom_isIntegral.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem ringKrullDim_le_of_ringHom_isIntegral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by sorry
