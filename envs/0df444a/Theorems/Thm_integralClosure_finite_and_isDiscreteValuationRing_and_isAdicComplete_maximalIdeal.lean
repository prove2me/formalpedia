-- Prove2me | Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
-- name    : integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/48a2c40d-8982-5595-bc5c-b6653d3bfece
-- title:
--   Integral closure of a complete DVR in a finite separable extension
-- statement:
--   Let $\mathcal O$ be a commutative domain which is a discrete valuation ring and is complete with respect to the adic filtration by the powers of its maximal ideal, let $L$ be a field which is an $\mathcal O$-algebra realising $L$ as the fraction field of $\mathcal O$ (i.e. the localisation of $\mathcal O$ at the set of non-zero-divisors), and let $L'$ be a field equipped with $\mathcal O$-algebra and $L$-algebra structures forming a scalar tower over $\mathcal O$, such that $L'$ is finite-dimensional over $L$ and the extension $L'/L$ is separable. Write $\mathcal O' = \mathrm{integralClosure}\ \mathcal O\ L'$ for the subalgebra of elements of $L'$ integral over $\mathcal O$. The theorem asserts two things simultaneously: first, $\mathcal O'$ is a finite $\mathcal O$-module; secondly, there exists a proof that $\mathcal O'$ is a discrete valuation ring, and, with respect to the resulting local structure, $\mathcal O'$ is complete for the adic filtration by the powers of its own maximal ideal. The existential in the second clause serves to make the maximal ideal of $\mathcal O'$ available in the statement of completeness.
--
--   This is the standard structure theorem for extensions of a complete discrete valuation ring in the separable case: the integral closure is again a complete discrete valuation ring, module-finite over the base. It supplies the coefficient rings used throughout the construction of $\ell$-adic Galois representations attached to eigenforms, where finite extensions of $\mathbb Z_p$ and their residue data are needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (L : Type*) [Field L] [Algebra 𝒪 L] [IsFractionRing 𝒪 L]
    (L' : Type*) [Field L'] [Algebra 𝒪 L'] [Algebra L L'] [IsScalarTower 𝒪 L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L'] :
    Module.Finite 𝒪 (integralClosure 𝒪 L') ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L'),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L'))
        (integralClosure 𝒪 L') := by sorry
