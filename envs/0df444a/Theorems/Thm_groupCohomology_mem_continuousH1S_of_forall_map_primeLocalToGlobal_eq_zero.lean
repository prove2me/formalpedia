-- Prove2me | Theorems.Thm_groupCohomology_mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero
-- name    : groupCohomology.mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/22c24168-95d3-5924-b9c3-a5550f2e7ec0
-- title:
--   Local triviality at Q gives classes unramified outside S
-- statement:
--   Let $k$ be a commutative ring, let $S$ and $Q$ be finite sets of rational primes, and let $M$ be a $k$-linear representation of the group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of ring automorphisms of `AlgebraicClosure ℚ` over $\mathbb{Q}$. Assume $M$ is smooth, in the sense that every $m \in M$ admits an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\rho(s)m = m$ for all $s$ in the fixing subgroup of $F$; and assume $M$ is unramified outside $S$, in the sense that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup) acts on $M$ as the identity. Let $x \in H^1(\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}), M)$ lie in `continuousH1S (S ∪ Q) M`, the image under the projection `H1π M` of the submodule `levelCocyclesS₁ (S ∪ Q) M` of $1$-cocycles. Suppose that for every $q \in Q$ the degree-one map on cohomology induced by the homomorphism `primeLocalToGlobal q` from $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (restriction of scalars to $\mathbb{Q}$ followed by restriction of normal automorphisms to $\overline{\mathbb{Q}}$), taken with the identity morphism of the restricted representation, annihilates $x$. Then $x \in$ `continuousH1S S M`.
--
--   This is the bookkeeping step which shows that a class of level $S \cup Q$ whose restriction to the local Galois group at each auxiliary prime $q \in Q$ vanishes is already of level $S$; combined with the characterisation of `continuousH1S S M` as the classes of locally constant cocycles that are coboundaries on all inertia subgroups above primes outside $S$, it identifies the Selmer conditions at the augmented level used in the Taylor–Wiles argument. It is used in the construction of sets of Taylor–Wiles primes, in [`ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist`](thm.html#ResidualGaloisRep.exists_taylorWilesPrimes_card_eq_finrank_continuousH1S_dualTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.mem_continuousH1S_of_forall_map_primeLocalToGlobal_eq_zero
    {k : Type} [CommRing k] (S Q : Finset Nat.Primes)
    (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1)
    (x : H1 M) (hx : x ∈ continuousH1S (S ∪ Q) M)
    (h0 : ∀ q ∈ Q, (groupCohomology.map (primeLocalToGlobal q)
      (𝟙 (Rep.res (primeLocalToGlobal q) M)) 1).hom x = 0) :
    x ∈ continuousH1S S M := by sorry
