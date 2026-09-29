-- Prove2me | Theorems.Thm_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
-- name    : groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/785ebc9d-1259-5c28-b188-58410c9b7a1f
-- title:
--   A generator of H²(Γ/S,C^S) from an inflated class
-- statement:
--   Let $k$ be a commutative ring, $\Gamma$ a finite group and $C$ a $k$-linear representation of $\Gamma$, and let $S,T\trianglelefteq\Gamma$ be normal subgroups with $\Gamma/S$ finite. Assume that the degree-one cohomology objects $H^1(S,C|_S)$ and $H^1(T,C|_T)$ of the restricted representations are zero. Let $n'$ be a nonzero natural number divisible by $n:=|\Gamma/S|$, and let $u'\in H^2(\Gamma/T,C^T)$ be a class whose additive order equals $n'$, where $C^T$ carries its natural $\Gamma/T$-action. Write $\mathrm{inf}_S$ and $\mathrm{inf}_T$ for the inflation maps in degree $2$ induced by $\Gamma\to\Gamma/S$, $\Gamma\to\Gamma/T$ together with the inclusions $C^S\hookrightarrow C$, $C^T\hookrightarrow C$, and $\mathrm{res}_S$ for the restriction $H^2(\Gamma,C)\to H^2(S,C|_S)$. Suppose $\mathrm{res}_S\bigl((n'/n)\cdot\mathrm{inf}_T(u')\bigr)=0$, that $H^2(\Gamma/S,C^S)$ is finite, and that its cardinality is at most $n$. Then there exists $y\in H^2(\Gamma/S,C^S)$ such that the cardinality of $H^2(\Gamma/S,C^S)$ is exactly $n$, the $k$-submodule spanned by $\{y\}$ is all of $H^2(\Gamma/S,C^S)$, and $\mathrm{inf}_S(y)=(n'/n)\cdot\mathrm{inf}_T(u')$.
--
--   This is the group-cohomological core of the "compositum and inflation" step in the Artin–Tate treatment of class formations, where $u'$ plays the role of the fundamental class of an auxiliary cyclic layer and the vanishing of the restriction is the arithmetic input. It is used by [`groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq`](thm.html#groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_carry_of_exists_norm_eq), which packages the same conclusion from a hypothesis about norms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem groupCohomology.exists_natCard_H2_eq_and_span_eq_top_of_map_res_inf_smul_eq_zero
    {k Γ : Type} [CommRing k] [Group Γ] [Fintype Γ] (C : Rep k Γ) (S T : Subgroup Γ) [S.Normal] [T.Normal]
    [Fintype (Γ ⧸ S)]
    (hS1 : IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (hT1 : IsZero (groupCohomology (Rep.res T.subtype C) 1))
    (n' : ℕ) (hn : Fintype.card (Γ ⧸ S) ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology (C.quotientToInvariants T) 2) (hu' : addOrderOf u' = n')
    (hres : (map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom
        ((n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u') = 0)
    (hfin : Finite (groupCohomology (C.quotientToInvariants S) 2))
    (hle : Nat.card (groupCohomology (C.quotientToInvariants S) 2) ≤ Fintype.card (Γ ⧸ S)) :
    ∃ y : groupCohomology (C.quotientToInvariants S) 2,
      Nat.card (groupCohomology (C.quotientToInvariants S) 2) = Fintype.card (Γ ⧸ S) ∧
      Submodule.span k {y} = ⊤ ∧
      (map (A := C.quotientToInvariants S) (B := C) (QuotientGroup.mk' S)
          (ofHom (C.ρ.quotientToInvariants_lift S)) 2).hom y =
        (n' / Fintype.card (Γ ⧸ S)) •
          (map (A := C.quotientToInvariants T) (B := C) (QuotientGroup.mk' T)
            (ofHom (C.ρ.quotientToInvariants_lift T)) 2).hom u' := by sorry
