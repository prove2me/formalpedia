-- Prove2me | Theorems.Thm_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top
-- name    : exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c6137eb5-0d30-55c3-84d0-38fbc9d69e68
-- title:
--   Image of bigwedgeᵈ N in bigwedgeᵈ M for corank-one N over a DVR
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, and let $M$ be an $R$-module which is free and finite over $R$ (given as an additive commutative group with an $R$-module structure). Let $d$ be a natural number with $\operatorname{finrank}_R M = d$, let $N$ be an $R$-submodule of $M$, and suppose there is an $R$-linear isomorphism $e \colon M/N \xrightarrow{\ \sim\ } R/\mathfrak m$, that is, $N$ has corank one with quotient the residue field. The assertion is an equality of submodules of the $d$-th exterior power $\bigwedge^d_R M$: the range of the map $\bigwedge^d_R N \to \bigwedge^d_R M$ induced by the inclusion `N.subtype` of $N$ into $M$ (the $d$-th exterior power functor applied to that inclusion) equals $\mathfrak m \cdot \top$, the submodule obtained by scaling the whole of $\bigwedge^d_R M$ by the maximal ideal. The isomorphism $e$ enters only through its existence; no compatibility with any chosen basis is required.
--
--   This is the simplest case of the theory of elementary divisors over a discrete valuation ring: a submodule whose quotient is the residue field is, in a suitable basis $b_0,\dots,b_{d-1}$ of $M$, of the form $\varpi R b_0 \oplus R b_1 \oplus \dots \oplus R b_{d-1}$ for a uniformiser $\varpi$, so that the top exterior power of the inclusion has image $\varpi \bigwedge^d_R M$. It serves the computation of norms of ideals, being used in [`Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing`](thm.html#Ideal.span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    {d : ℕ} (hd : Module.finrank R M = d)
    (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R)) :
    LinearMap.range (exteriorPower.map d N.subtype) = IsLocalRing.maximalIdeal R • ⊤ := by sorry
