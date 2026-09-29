-- Prove2me | Theorems.Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
-- name    : groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c23dd5a3-b17a-5fdd-85b4-2b1837d319be
-- title:
--   Descent of a degree-three cochain along an S-level prime to p
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and write $\Gamma = \mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ for the automorphism group of `AlgebraicClosure ℚ` over $\mathbb Q$. Let $N$ be a $\mathbb Z/p$-linear representation of $\Gamma$ and let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ which is unramified outside $S$ in the sense that $K$ is finite-dimensional over $\mathbb Q$ and, for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $A$, the image in $\Gamma$ of the inertia subgroup of $A$ over $\mathbb Q$ lies in the fixing subgroup $\Gamma_K$ of $K$; assume $\Gamma_K$ has finite index and $p \nmid [\Gamma : \Gamma_K]$. Let $u : \Gamma^3 \to N$ be a function which is level constant, i.e. there is an intermediate field $F$, unramified outside $S$ in the same sense, with $u(g \cdot s) = u(g)$ for all $g, s \in \Gamma^3$ whose components $s_i$ all lie in $\Gamma_F$ (the product being componentwise), and assume $u$ is a cocycle: the differential $d^{3,4}$ of the inhomogeneous cochain complex of $N$ kills $u$. Assume further that there is a level-constant function $w' : \Gamma_K^2 \to N$ (level constancy being invariance under componentwise right multiplication by elements of $\Gamma_F$ for some $F$ unramified outside $S$) whose differential $d^{2,3}$, computed in the inhomogeneous cochain complex of the restriction of $N$ to $\Gamma_K$, equals the restriction of $u$ to $\Gamma_K^3$. Then there exists a level-constant $w : \Gamma^2 \to N$ with $d^{2,3} w = u$ in the inhomogeneous cochain complex of $N$.
--
--   This is the transfer (corestriction–restriction) step in degree three for Galois cohomology computed with level-constant inhomogeneous cochains: a degree-three cochain over $\Gamma$ that becomes a coboundary after restriction to the subgroup attached to an $S$-level of degree prime to $p$ is already a coboundary, which amounts to injectivity of restriction to such a level. It feeds the vanishing statement proved in [`groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel`](thm.html#groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_forall_cyclotomicLevel), where the level is chosen as the fixed field of a $p$-Sylow subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_res_fixingSubgroup_three
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (N : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S)
    [K.fixingSubgroup.FiniteIndex] (hpK : ¬ p ∣ K.fixingSubgroup.index)
    (u : (Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N)
    (hlc : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 3 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ i, s i ∈ F.fixingSubgroup) → u (g * s) = u g)
    (hcoc : ((inhomogeneousCochains N).d 3 4).hom u = 0)
    (w' : (Fin 2 → K.fixingSubgroup) → N)
    (hlc' : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ g s : Fin 2 → K.fixingSubgroup,
        (∀ i, (s i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup) → w' (g * s) = w' g)
    (hw' : ((inhomogeneousCochains (Rep.res K.fixingSubgroup.subtype N)).d 2 3).hom w'
             = fun h : Fin 3 → K.fixingSubgroup =>
                 u (fun i => (h i : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ w : (Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) → N,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ g s : Fin 2 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
          (∀ i, s i ∈ F.fixingSubgroup) → w (g * s) = w g) ∧
      ((inhomogeneousCochains N).d 2 3).hom w = u := by sorry
