-- Prove2me | Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
-- name    : groupCohomology.continuousH2SrInflation_H2pi_eq_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/1862fdf4-48f0-58bb-9045-e421a11f8330
-- title:
--   Inflations of two S-level 2-cocycles with equal values agree
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $r : G \to \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ a group homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$, $S$ a finite set of rational primes and $M$ a representation of $G$ over $k$. Let $F, F'$ be intermediate fields of $\overline{\mathbb{Q}}/\mathbb{Q}$, each normal over $\mathbb{Q}$ and each satisfying `IsUnramifiedOutside S`, i.e. finite-dimensional over $\mathbb{Q}$ and such that for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, the image in $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ is contained in the fixing subgroup of $F$ (resp. $F'$). Write $U_F = r^{-1}(F^{\mathrm{fix}})$ and let $f$ be an inhomogeneous $2$-cocycle of the $G/U_F$-representation on the $U_F$-invariants of $M$, and likewise $f'$ for $F'$. Assume that for all $g, h \in G$ the elements $f'(\bar g, \bar h)$ and $f(\bar g, \bar h)$ coincide when regarded in $M$. Then the two inflation maps `continuousH2SrInflation` send the classes of $f'$ and of $f$ to the same element of the $k$-module `continuousH2Sr r S M`. No inclusion between $F$ and $F'$ is assumed; the hypothesis relating them is only the equality of the underlying values.
--
--   This is the cocycle-wise form of the compatibility of the finite-level inflations with the transition maps between $S$-levels, which makes the system of inflations into the continuous second cohomology coherent and allows a class to be represented at a deeper layer. It is used in the arithmetic of levels, for instance in the construction and uniqueness of local Brauer invariants and in the production of layer presentations of cohomology classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.continuousH2SrInflation_H2pi_eq_of_le
    {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S) [Normal ℚ F] [Normal ℚ F']
    (f : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) (f' : cocycles₂ (M.quotientToInvariants (F'.fixingSubgroup.comap r)))
    (hff' : ∀ g h : G, ((f' ((g : G ⧸ F'.fixingSubgroup.comap r), (h : G ⧸ F'.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)
      = ((f ((g : G ⧸ F.fixingSubgroup.comap r), (h : G ⧸ F.fixingSubgroup.comap r)) : M.quotientToInvariants _) : M)) :
    continuousH2SrInflation r S M F' hF' (H2π _ f') = continuousH2SrInflation r S M F hF (H2π _ f) := by sorry
