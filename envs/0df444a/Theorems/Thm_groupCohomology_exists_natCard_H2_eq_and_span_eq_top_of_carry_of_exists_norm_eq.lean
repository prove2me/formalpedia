-- Prove2me | Theorems.Thm_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
-- name    : groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/caffab65-9598-56f2-9d05-422e90b8f00d
-- title:
--   Carry class upstairs plus a norm condition forces H²(Γ/S,C^S) cyclic of order [Γ:S]
-- statement:
--   Let $\Gamma$ be a finite group, $C$ a $\mathbb{Z}$-linear representation of $\Gamma$, and $S,T\trianglelefteq\Gamma$ normal subgroups with $\Gamma/S$ finite and $S\cap T=1$, such that $H^1$ of the restriction of $C$ to $S$ and to $T$ both vanish. Assume $s\in\Gamma/T$ is of finite order and every element of $\Gamma/T$ is an integral power of $s$, and likewise $t\in S$ is of finite order and generates $S$; let $n'=\operatorname{ord}(s)$ and assume $|\Gamma/S|\mid n'$. Let $a_{0T}$ lie in the $T$-invariants $C^T$ (a representation of $\Gamma/T$) with image $a_0\in C$ under the canonical inclusion, and suppose $a_0$ is $\Gamma$-invariant. Writing $\operatorname{cyclicLog}(g)$ for the unique exponent in $[0,n')$ with $s^{\operatorname{cyclicLog}(g)}=g$, assume the carry function $(g,h)\mapsto a_{0T}$ if $\operatorname{cyclicLog}(g)+\operatorname{cyclicLog}(h)\ge n'$ and $0$ otherwise is a $2$-cocycle of $\Gamma/T$ with values in $C^T$, and that its class in $H^2(\Gamma/T,C^T)$ has additive order exactly $n'$. Assume further that $(n'/|\Gamma/S|)\,a_0$ is a norm from $\langle t\rangle$: there is $b\in C$ with $\sum_{i<\operatorname{ord}(t)}t^i b=(n'/|\Gamma/S|)\,a_0$. Finally assume $H^2(\Gamma/S,C^S)$ is finite of cardinality at most $|\Gamma/S|$. Then there exists $y\in H^2(\Gamma/S,C^S)$ such that this cardinality equals $|\Gamma/S|$, the $\mathbb{Z}$-span of $\{y\}$ is everything, and the inflation map in degree $2$ attached to $\Gamma\to\Gamma/S$ and $C^S\hookrightarrow C$ sends $y$ to $(n'/|\Gamma/S|)$ times the inflation to $H^2(\Gamma,C)$ of the above carry class.
--
--   This is the abstract form, in carry-cocycle language, of the Artin–Tate construction of the fundamental class of an arbitrary finite layer out of an auxiliary cyclic layer, with all the arithmetic input concentrated in the norm hypothesis on $(n'/|\Gamma/S|)\,a_0$. It is applied to the idèle class group in [`M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup`](thm.html#M4aHerbrand.exists_natCard_H2_eq_card_and_span_eq_top_ideleClassGroup) and its $p$-group variant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq
    {Γ : Type} [Group Γ] [Fintype Γ] (C : Rep ℤ Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)] (hST : S ⊓ T = ⊥)
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (s : Γ ⧸ T) (hs : ∀ g : Γ ⧸ T, g ∈ Subgroup.zpowers s) (hsfin : IsOfFinOrder s)
    (t : S) (ht : ∀ g : S, g ∈ Subgroup.zpowers t) (htfin : IsOfFinOrder t)
    (n' : ℕ) (hn' : orderOf s = n') (hn : Fintype.card (Γ ⧸ S) ∣ n')
    (a₀T : C.quotientToInvariants T) (a₀ : C) (ha₀T : (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _) a₀T = a₀)
    (ha₀ : ∀ g : Γ, C.ρ g a₀ = a₀)
    (hzT : carryFun s hs hsfin a₀T ∈ cocycles₂ (C.quotientToInvariants T))
    (hord : addOrderOf ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) = n')
    (hnorm : ∃ b : C, (∑ i ∈ Finset.range (orderOf t), C.ρ ((t : Γ) ^ i) b) = (n' / Fintype.card (Γ ⧸ S)) • a₀)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span ℤ {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants S).hV1 C.hV1 (C.quotientToInvariants S).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ S _)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (@Rep.ofHom ℤ Γ _ _ _ _ (C.quotientToInvariants T).hV1 C.hV1 (C.quotientToInvariants T).hV2 C.hV2 _ _ (@Representation.quotientToInvariants_lift ℤ Γ _ _ C.V C.hV1 C.hV2 C.ρ T _)) 2).hom
              ((H2π (C.quotientToInvariants T)).hom ⟨carryFun s hs hsfin a₀T, hzT⟩) := by sorry
