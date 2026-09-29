-- Prove2me | Theorems.Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
-- name    : groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/08b4d311-8ae4-5e9a-a158-5f7cde2d384b
-- title:
--   Vanishing of H³(G_{ℚ,S},N) from the cyclotomic levels
-- statement:
--   Let $p$ be a prime and let $S$ be a finite set of rational primes containing $p$. Write $\Gamma=\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ for the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$, and call an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ unramified outside $S$ when $F$ is finite over $\mathbb Q$ and, for every prime $q\notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\Gamma$ of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup of $F$. A function $u$ on $n$-tuples of group elements is called level-constant when there is an $F$ unramified outside $S$ with $u(g\cdot s)=u(g)$ for all $g,s$ whose components $s_i$ all lie in the fixing subgroup of $F$. The hypothesis `hlev` assumes: for every intermediate field $K$ that is unramified outside $S$ (finiteness over $\mathbb Q$ being also stated separately) on whose fixing subgroup the mod-$p$ cyclotomic character `cycloChar p` is trivial, every level-constant $u\colon (K\text{-fixing subgroup})^3\to\mathbb Z/p$ with values in the trivial representation and with $d^{3,4}u=0$ in the inhomogeneous cochain complex is $d^{2,3}w$ for some level-constant $w$ on pairs. Let further $N$ be a representation of $\Gamma$ over $\mathbb Z/p$, finite-dimensional over $\mathbb Z/p$, such that every $m\in N$ is fixed by $\rho(s)$ for all $s$ in the fixing subgroup of some finite subextension, and such that $\rho(s)=1$ for every $s$ in the inertia subgroup over $\mathbb Q$ of any valuation subring having a prime $q\notin S$ as a non-unit. Then for every level-constant $u\colon\Gamma^3\to N$ with $d^{3,4}u=0$ there is a level-constant $w\colon\Gamma^2\to N$ with $d^{2,3}w=u$.
--
--   This is Serre's reduction, in the level-constant inhomogeneous cochain model of the cohomology of the $S$-ramified Galois group of $\mathbb Q$, of the vanishing of $H^3$ with smooth unramified-outside-$S$ mod-$p$ coefficients to the case of trivial $\mathbb Z/p$ coefficients over the finite levels on which the mod-$p$ cyclotomic character is trivial. It is the algebraic half of [`groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two`](thm.html#groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two), which supplies the arithmetic input for odd $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (hlev : ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)), K.IsUnramifiedOutside S → FiniteDimensional ℚ ↥K →
      (∀ s ∈ K.fixingSubgroup, cycloChar p s = 1) →
      ∀ u : (Fin 3 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
        (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 3 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → u (g * s) = u g) →
        ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 3 4).hom u = 0 →
        ∃ w : (Fin 2 → ↥K.fixingSubgroup) → Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p),
          (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
          ∀ g s : Fin 2 → ↥K.fixingSubgroup,
            (∀ i, ((s i : ↥K.fixingSubgroup) : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
          ((inhomogeneousCochains (Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p))).d 2 3).hom w = u)
    (N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) [FiniteDimensional (ZMod p) N]
    (hsm : ∀ m : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s ∈ F.fixingSubgroup, N.ρ s m = m)
    (hur : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
      A.LiesOverPrime (q : ℕ) → ∀ s ∈ A.inertiaSubgroupIn ℚ, N.ρ s = 1)
    (u : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ i, s i ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0) :
    ∃ w : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ i, s i ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains N).d 2 3).hom w = u := by sorry
