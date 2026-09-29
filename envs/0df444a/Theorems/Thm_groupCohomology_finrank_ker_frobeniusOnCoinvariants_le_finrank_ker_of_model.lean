-- Prove2me | Theorems.Thm_groupCohomology_finrank_ker_frobeniusOnCoinvariants_le_finrank_ker_of_model
-- name    : groupCohomology.finrank_ker_frobeniusOnCoinvariants_le_finrank_ker_of_model
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/4acfd17e-3035-5234-8ac6-b3fada037399
-- title:
--   Eigenspace bound for Frobenius on ̄ t-coinvariants via a model
-- statement:
--   Let $k$ be a field, $G$ a group and $M$ a finite-dimensional $k$-linear representation of $G$ with action $\rho$. Let $U,W\le G$ be normal subgroups of finite index, suppose $\rho(u)=1$ for all $u\in U$, and let $q$ be a prime with $q\ne 0$ in $k$ such that every $w\in W$ satisfies $w^{q^a}\in U$ for some $a\in\mathbb N$. Let $t,\varphi\in G$ be such that, writing $\bar t,\bar\varphi$ for their images in $G/W$, one has $\bar\varphi\,\bar t\,\bar\varphi^{-1}\in\langle\bar t\rangle$ (the subgroup of integer powers of $\bar t$). Let $D$ be a finite-dimensional $k$-vector space, $\pi\colon M\to D$ a $k$-linear map with $\ker\pi\subseteq\bigl(\sum_{w\in W}\operatorname{im}(\rho(w)-1)\bigr)+\operatorname{im}(\rho(t)-1)$ and $\operatorname{im}(\rho(t)-1)\subseteq\ker\pi$, and let $\varphi_D\colon D\to D$ be $k$-linear with $\varphi_D\circ\pi=\pi\circ\rho(\varphi)$. Finally let $m\in\mathbb N$ and $b\in k$ satisfy $mb=1$ in $k$. Write $F$ for the endomorphism of $M^W/\operatorname{im}(\bar t-1)$ induced by the action of $\bar\varphi$ on the representation of $G/W$ on $M^W$, i.e. `frobeniusOnCoinvariants (M.quotientToInvariants W) (QuotientGroup.mk t) (QuotientGroup.mk φ)`, the map obtained from $\rho(\bar\varphi)$ by passage to the quotient by the image of $\rho(\bar t)-1$. Then $\dim_k\ker(mF-1)\le\dim_k\ker(\varphi_D-b\cdot\mathrm{id})$. Note that $U\le W$ and surjectivity of $\pi$ are not assumed.
--
--   The bound transfers an eigenspace dimension for the Frobenius action on the $\bar t$-coinvariants of the $W$-invariants of $M$ to any model $(D,\pi,\varphi_D)$ of the quotient of $M$ by the $W$-augmentation together with $(\rho(t)-1)M$, the hypotheses on $q$ making averaging over the finite quotient of $W$ available. It is used by [`groupCohomology.finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist`](thm.html#groupCohomology.finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist), where the Frobenius-twisted term produced by the cyclic-quotient cohomology estimate is rewritten as an invariants dimension for a Tate-twisted dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_ker_frobeniusOnCoinvariants_le_finrank_ker_of_model.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateTwist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.finrank_ker_frobeniusOnCoinvariants_le_finrank_ker_of_model
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (U W : Subgroup G) [U.Normal] [W.Normal] [U.FiniteIndex] [W.FiniteIndex]
    (hU : ∀ u ∈ U, M.ρ u = 1)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0) (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t φ : G)
    (hst : (QuotientGroup.mk φ : G ⧸ W) * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹
      ∈ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ W))

    (D : Type u) [AddCommGroup D] [Module k D] [FiniteDimensional k D]
    (π : M →ₗ[k] D)
    (hker : LinearMap.ker π ≤ (⨆ w ∈ W, LinearMap.range (M.ρ w - 1)) ⊔ LinearMap.range (M.ρ t - 1))
    (hπt : LinearMap.range (M.ρ t - 1) ≤ LinearMap.ker π)
    (φD : D →ₗ[k] D) (hφD : φD ∘ₗ π = π ∘ₗ M.ρ φ)
    (m : ℕ) (b : k) (hmb : (m : k) * b = 1) :
    finrank k (LinearMap.ker (m • frobeniusOnCoinvariants (M.quotientToInvariants W)
        (QuotientGroup.mk t) (QuotientGroup.mk φ) hst - 1))
      ≤ finrank k (LinearMap.ker (φD - b • 1)) := by sorry
