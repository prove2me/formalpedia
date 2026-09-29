-- Prove2me | Theorems.Thm_groupCohomology_H2res_comp_H2inf_eq_zero
-- name    : groupCohomology.H2res_comp_H2inf_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/ed6daa84-5449-5eb5-99e7-918555bcc9de
-- title:
--   Degree-two inflation followed by restriction vanishes
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $A$ be a $k$-linear representation of $G$, and let $S$ be a normal subgroup of $G$. Two functorial maps on degree-$2$ group cohomology are formed. The first is `groupCohomology.map` applied to the quotient homomorphism $G \to G/S$ together with the morphism of $G/S$-representations `Rep.ofHom (A.ρ.quotientToInvariants_lift S)` from `A.quotientToInvariants S`, the representation of $G/S$ on the $S$-invariants $A^S$, to the restriction of $A$ along $G \to G/S$; this is inflation $H^2(G/S, A^S) \to H^2(G, A)$. The second is `groupCohomology.map` applied to the inclusion $S \hookrightarrow G$ together with the identity morphism of `Rep.res S.subtype A`; this is restriction $H^2(G, A) \to H^2(S, A)$. The assertion is that the composite of the first followed by the second is the zero morphism of $k$-modules.
--
--   This is one half of the inflation–restriction (Hochschild–Serre) exact sequence in degree $2$: the composite $\mathrm{res} \circ \mathrm{inf}$ vanishes, so that inflation lands in the kernel of restriction. It is used in [`groupCohomology.finite_H2_and_natCard_H2_le`](thm.html#groupCohomology.finite_H2_and_natCard_H2_le), where finiteness of and a bound on $H^2$ are obtained from the corresponding data for $H^2(G/S, A^S)$ and $H^2(S, A)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_H2res_comp_H2inf_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep

theorem groupCohomology.H2res_comp_H2inf_eq_zero
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 ≫
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 = 0 := by sorry
