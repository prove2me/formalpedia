-- Prove2me | Theorems.Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two
-- name    : groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/551c1b5d-1371-5be0-8f82-52b11c366a5d
-- title:
--   Vanishing of H³(G_{ℚ,S},N) for odd p, at cochain level
-- statement:
--   Let $p$ be an odd prime and let $S$ be a finite set of rational primes with $p \in S$. Let $N$ be a finite-dimensional representation of $\Gamma = \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ over $\mathbb{Z}/p$ (with $\overline{\mathbb{Q}}$ realised as `AlgebraicClosure ℚ`), subject to two arithmetic hypotheses: smoothness, i.e. every $m \in N$ is fixed by $\operatorname{Gal}(\overline{\mathbb{Q}}/F)$ for some intermediate field $F$ of finite degree over $\mathbb{Q}$; and unramifiedness outside $S$, i.e. for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\Gamma$ of the inertia subgroup inside the decomposition subgroup) acts on $N$ as the identity. Let $u : \Gamma^3 \to N$ be a $3$-cochain which is level-constant outside $S$: for some intermediate field $F$ of finite degree over $\mathbb{Q}$ whose fixing subgroup contains all inertia subgroups at primes outside $S$, one has $u(g \cdot s) = u(g)$ whenever all three components of $s$ lie in $\operatorname{Gal}(\overline{\mathbb{Q}}/F)$. Assume $u$ is a cocycle, i.e. the differential $d^{3,4}$ of Mathlib's complex of inhomogeneous cochains of $N$ kills $u$. Then there is a $2$-cochain $w : \Gamma^2 \to N$, level-constant outside $S$ in the same sense (for some such $F$, possibly another), with $d^{2,3} w = u$.
--
--   This is the statement $H^3(G_{\mathbb{Q},S},N) = 0$ for odd $p$, equivalently $\operatorname{cd}_p G_{\mathbb{Q},S} \le 2$, expressed in the model of inhomogeneous cochains on the full Galois group that are constant modulo a level $\operatorname{Gal}(\overline{\mathbb{Q}}/F)$ with $F$ unramified outside $S$. It is used to prove surjectivity of the map on continuous $H^2$ attached to a short exact sequence of such representations, for $p \neq 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two.lean

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

theorem groupCohomology.exists_isLevelConstant_inhomogeneousCochains_d_eq_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
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
