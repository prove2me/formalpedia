-- Prove2me | Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
-- name    : groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/5ad7c905-813d-58c1-92d9-d1d1ab3ae544
-- title:
--   Smooth finite Galois module unramified outside S trivialises over finite F
-- statement:
--   Let $S$ be a finite set of rational primes, let $k$ be a commutative ring, and let $M$ be a $k$-linear representation $\rho =$ `M.ρ` of the group $\Gamma = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, with $M$ finite as a $k$-module. Assume two things. First, smoothness: for every $m \in M$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $s$ fixing $F$ pointwise satisfies $\rho(s)m = m$. Second, unramifiedness outside $S$: for every prime $q \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, and every $g$ in the image in $\Gamma$ of the inertia subgroup of the decomposition subgroup of $A$ over $\mathbb{Q}$, one has $\rho(g) = 1$. The conclusion asserts the existence of a single intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ such that $F$ is finite-dimensional over $\mathbb{Q}$, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ having $q$ as a non-unit the above inertia image is contained in the pointwise stabiliser of $F$, and $\rho(s) = 1$ for every $s$ fixing $F$ pointwise.
--
--   This is the standard passage from a smooth finite Galois module unramified outside $S$ to a finite level: the representation factors through $\operatorname{Gal}(F/\mathbb{Q})$ for one finite extension $F/\mathbb{Q}$ whose ramification is confined to $S$. It supplies the finite-level data on which the continuous and unramified cohomology groups of the project are built, and is used in the construction of level-constant cochains, the long exact sequences for continuous cohomology of short exact sequences, and the finite-dimensionality of the relevant second cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

theorem groupCohomology.exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth (S : Finset Nat.Primes)
    {k : Type} [CommRing k] (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [Module.Finite k M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s m = m)
    (hMur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ g ∈ A.inertiaSubgroupIn ℚ, M.ρ g = 1) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s ∈ F.fixingSubgroup, M.ρ s = 1 := by sorry
