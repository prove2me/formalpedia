-- Prove2me | Theorems.Thm_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level
-- name    : groupCohomology.isMulCoboundary1_of_isMulCocycle1_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/6cced071-6b67-5f9c-b452-bdb271dfbb2c
-- title:
--   Hilbert 90 for locally constant cocycles
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra that is Galois over $K$ (separable and normal, with no finiteness assumed), and let $f : (L \simeq_{\mathrm{alg}[K]} L) \to L^{\times}$ be a function on the Galois group with values in the units of $L$. Assume first that $f$ is a multiplicative $1$-cocycle for the natural action of $K$-algebra automorphisms on $L^{\times}$, i.e. $f(\sigma\tau) = \sigma(f(\tau))\, f(\sigma)$ for all $\sigma,\tau$. Assume second that $f$ is right-invariant under the fixing subgroup of some finite subextension: there exists an intermediate field $E$ of $L/K$ with $E$ finite-dimensional over $K$ such that $f(\sigma\tau) = f(\sigma)$ whenever $\tau$ lies in the subgroup of automorphisms fixing $E$ pointwise. The conclusion is that $f$ is a multiplicative $1$-coboundary: there exists $\alpha \in L^{\times}$ with $\sigma(\alpha)/\alpha = f(\sigma)$ for every $K$-automorphism $\sigma$ of $L$.
--
--   This is Hilbert's Theorem 90 in its continuous form for a possibly infinite Galois extension: the second hypothesis says exactly that $f$ is locally constant for the Krull topology, and the conclusion is the vanishing of the corresponding continuous $H^1$ with coefficients in $L^{\times}$. It is used in the treatment of Kummer representations, both to produce a coboundary witness for cocycles trivial on the fixing subgroup of a finite subextension and in the analysis of injectivity and image of the induced map on continuous $H^2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology

theorem groupCohomology.isMulCoboundary1_of_isMulCocycle1_of_level
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {f : (L ≃ₐ[K] L) → Lˣ} (hf : IsMulCocycle₁ f)
    (hlc : ∃ E : IntermediateField K L, FiniteDimensional K E ∧
      ∀ σ τ : L ≃ₐ[K] L, τ ∈ E.fixingSubgroup → f (σ * τ) = f σ) :
    IsMulCoboundary₁ f := by sorry
