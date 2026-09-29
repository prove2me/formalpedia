-- Prove2me | Theorems.Thm_groupCohomology_nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom
-- name    : groupCohomology.nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/1be300ff-07d9-5695-bb0d-7fa753e651df
-- title:
--   H¹ of a trivial module as equivariant level-constant homomorphisms
-- statement:
--   Let $p$ be a prime, $S$ a finite set of primes, and $K, L$ intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`; write $\Gamma_K$ for `K.fixingSubgroup` and $\Gamma_{L,K}$ for `L.fixingSubgroup.subgroupOf K.fixingSubgroup`, the subgroup of $\Gamma_K$ of elements whose underlying automorphism fixes $L$. Let $M$ be a representation of $\Gamma_K$ over $\mathbb{Z}/p$ such that $M.\rho\,s = 1$ for every $s \in \Gamma_K$ lying in `L.fixingSubgroup`. Let $V$ be a $\mathbb{Z}/p$-submodule of $H^1(\Gamma_{L,K}, M)$ (cohomology of the restriction of $M$ along the inclusion) assumed to satisfy: $x \in V$ if and only if there is a $1$-cocycle $c$ with `H1π` $c = x$ such that for each $g \in \Gamma_K$ some $a \in M$ satisfies $M.\rho\,g\,(c\,t) - c\,s = M.\rho\,s\,a - a$ whenever $s, t \in \Gamma_{L,K}$ with $g^{-1} s g = t$. Then there exists a $\mathbb{Z}/p$-linear isomorphism between the intersection of $V$ with `continuousH1Sr` for the composite $\Gamma_{L,K} \to \Gamma_K \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ — the image under `H1π` of the submodule `levelCocyclesSr₁` of $1$-cocycles satisfying the $S$-level condition — and the submodule `eqLevelConstantHom` of maps $\varphi : \Gamma_{L,K} \to M$ that are additive, satisfy `IsLevelConstantSr₁` at $S$, and obey $M.\rho\,g\,(\varphi\,t) = \varphi\,s$ for all $g \in \Gamma_K$ and $s,t \in \Gamma_{L,K}$ with $g^{-1} s g = t$. The isomorphism is asserted only to exist.
--
--   This is the identification of the $S$-level part of $H^1$ of a module with trivial action, cut out by the condition defining $V$, with the space of $\Gamma_K$-equivariant additive $S$-level-constant maps $\Gamma_{L,K} \to M$; it is the cohomology-to-homomorphisms step in the Kummer-theoretic computation of a Selmer module. It is used in [`NumberField.LevelArith.finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor`](thm.html#NumberField.LevelArith.finiteDimensional_and_finrank_continuousH1Sr_res_inf_eq_finrank_invariants_selmerRep_tensor), where the dimension of the corresponding $H^1$ subspace is compared with that of a space of invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_GroupCohomology_LevelConstantHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem groupCohomology.nonempty_continuousH1Sr_inf_linearEquiv_eqLevelConstantHom
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (M : Rep.{0} (ZMod p) ↥K.fixingSubgroup)
    (hM : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → M.ρ s = 1)
    (V : Submodule (ZMod p) (H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M)))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M), H1π _ c = x ∧
      ∀ g : ↥K.fixingSubgroup, ∃ a : M, ∀ s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t → M.ρ g (c t) - c s = M.ρ (s : ↥K.fixingSubgroup) a - a) :
    Nonempty (↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
        (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M) ⊓ V) ≃ₗ[ZMod p]
      ↥(eqLevelConstantHom K.fixingSubgroup.subtype S (L.fixingSubgroup.subgroupOf K.fixingSubgroup) M)) := by sorry
