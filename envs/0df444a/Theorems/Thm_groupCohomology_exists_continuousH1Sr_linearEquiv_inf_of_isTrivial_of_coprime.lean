-- Prove2me | Theorems.Thm_groupCohomology_exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime
-- name    : groupCohomology.exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/d9a854df-19b0-54eb-841e-be5713676247
-- title:
--   S-level H¹ via restriction to an index-prime-to-p subgroup
-- statement:
--   Fix a prime $p$ and a finite set $S$ of rational primes, and let $K$ and $L$ be intermediate fields of $\overline{\mathbb{Q}}/\mathbb{Q}$. Assume `L.IsUnramifiedOutside S`, i.e. $L/\mathbb{Q}$ is finite and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$. Write $\Gamma_K$, $\Gamma_L$ for the fixing subgroups and $H = \Gamma_L \cap \Gamma_K$, viewed as a subgroup of $\Gamma_K$; assume $H$ is normal of finite index in $\Gamma_K$ and that the relative index of $\Gamma_L$ in $\Gamma_K$ is coprime to $p$. Let $M$ be a $\mathbb{Z}/p$-representation of $\Gamma_K$ on which every element of $\Gamma_K$ lying in $\Gamma_L$ acts trivially, and let $V$ be a $\mathbb{Z}/p$-submodule of $H^1(H, M|_H)$ such that $x \in V$ holds exactly when $x$ is the class of some $1$-cocycle $c$ for which, for every $g \in \Gamma_K$, there is $a \in M$ with $\rho(g)(c\,t) - c\,s = \rho(s)a - a$ whenever $s, t \in H$ satisfy $g^{-1} s g = t$. The conclusion asserts a $\mathbb{Z}/p$-linear isomorphism $e$ from `continuousH1Sr` of $\Gamma_K \hookrightarrow \operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ at $S$ and $M$ — the image under `H1π` of the submodule `levelCocyclesSr₁` of $1$-cocycles attached to that datum — onto the intersection of $V$ with the corresponding submodule for the composite $H \hookrightarrow \Gamma_K \hookrightarrow \operatorname{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ and $M|_H$, which moreover is compatible with restriction: for every $y$, the class underlying $e\,y$ is the image of $y$ under the restriction map `(H1InfRes M H).g.hom`.
--
--   This is the inflation–restriction (Hochschild–Serre) comparison in degree one for a normal subgroup of index prime to $p$, refined so that the $S$-level condition on a class may be read off from its restriction, the point being that $M$ is trivial on $\Gamma_L$ and $L$ is unramified outside $S$. It is used in the computation of the dimension of `continuousH1Sr` for a twist, where finiteness and ranks are transported across this isomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem groupCohomology.exists_continuousH1Sr_linearEquiv_inf_of_isTrivial_of_coprime
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (M : Rep.{0} (ZMod p) ↥K.fixingSubgroup)
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → M.ρ s = 1)
    (V : Submodule (ZMod p) (H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M)))
    (hV : ∀ x, x ∈ V ↔ ∃ c : cocycles₁ (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M), H1π _ c = x ∧
      ∀ g : ↥K.fixingSubgroup, ∃ a : M, ∀ s t : ↥(L.fixingSubgroup.subgroupOf K.fixingSubgroup),
        (g⁻¹ * s * g : ↥K.fixingSubgroup) = t → M.ρ g (c t) - c s = M.ρ (s : ↥K.fixingSubgroup) a - a) :
    ∃ e : ↥(continuousH1Sr K.fixingSubgroup.subtype S M) ≃ₗ[ZMod p]
      ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
          (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M) ⊓ V),
      ∀ y : ↥(continuousH1Sr K.fixingSubgroup.subtype S M),
        ((e y : ↥(continuousH1Sr (K.fixingSubgroup.subtype.comp (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype) S
            (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M) ⊓ V)) :
          H1 (Rep.res (L.fixingSubgroup.subgroupOf K.fixingSubgroup).subtype M)) =
        (H1InfRes M (L.fixingSubgroup.subgroupOf K.fixingSubgroup)).g.hom (y : H1 M) := by sorry
