-- Prove2me | Theorems.Thm_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
-- name    : groupCohomology.dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/58f1b9a1-e8f4-5cee-94fb-9de2b6b34102
-- title:
--   Unipotent first-order lifts on I are coboundaries there
-- statement:
--   Let $k$ be a field and $V$ a $k$-vector space with $\operatorname{finrank}_k V = 2$, let $G$ be a group, and let $\rho_0 : G \to \operatorname{End}_k(V)$ be a monoid homomorphism into the multiplicative monoid of endomorphisms, with $\rho_0^{\times} : G \to \operatorname{End}_k(V)^{\times}$ the associated homomorphism into the units. Let $\rho : G \to (\operatorname{End}_k(V)[\varepsilon])^{\times}$ be a homomorphism into the units of the dual numbers over $\operatorname{End}_k(V)$ which is a dual lift of $\rho_0^{\times}$, i.e. the constant part of $\rho(g)$ equals $\rho_0(g)$ for every $g \in G$. Let $I \le G$ be a subgroup such that the image subgroup $\rho(I)$ is cyclic, such that $\rho_0(g) \ne 1$ for at least one $g \in I$, and such that $(\rho_0(g) - 1)^2 = 0$ for all $g \in I$. Then the condition that $(\rho(g) - 1)^2 = 0$ in $\operatorname{End}_k(V)[\varepsilon]$ for every $g \in I$ is equivalent to the existence of an $m \in \operatorname{End}_k(V)$ with $$\varepsilon\text{-part}(\rho(g)) \cdot \rho_0(g)^{-1} = m - \rho_0(g)\, m\, \rho_0(g^{-1}) \qquad \text{for all } g \in I,$$ where the left-hand side is the associated $1$-cochain of the lift, the product of the $\varepsilon$-component of $\rho(g)$ with the inverse of the unit $\rho_0^{\times}(g)$.
--
--   This is the tangent-space form of the local deformation condition at a prime of unipotent (semistable, type (A)) ramification: among first-order lifts of a representation whose restriction to $I$ is non-trivial unipotent with cyclic image under the lift, those on which $I$ still acts with $(\rho(g)-1)^2 = 0$ are exactly those whose $1$-cochain becomes a coboundary for the adjoint action after restriction to $I$. It is used in the study of unipotence on inertia, via [`GaloisRepAdic.exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt`](thm.html#GaloisRepAdic.exists_submodule_finrank_le_invariants_mem_of_isUnipotentOnInertiaAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj.lean

import Definitions.Def_GroupCohomology_TangentSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 2)
    {G : Type} [Group G] (ρ₀ : G →* Module.End k V)
    (ρ : G →* (DualNumber (Module.End k V))ˣ) (hρ : IsDualLift ρ₀.toHomUnits ρ)
    (I : Subgroup G) (hcyc : IsCyclic (I.map ρ))
    (hne : ∃ g ∈ I, ρ₀ g ≠ 1) (hunip : ∀ g ∈ I, (ρ₀ g - 1) ^ 2 = 0) :
    (∀ g ∈ I, ((ρ g : DualNumber (Module.End k V)) - 1) ^ 2 = 0) ↔
      ∃ m : Module.End k V, ∀ g ∈ I,
        dualLiftToCochain ρ₀.toHomUnits ρ g = m - ρ₀ g * m * ρ₀ g⁻¹ := by sorry
