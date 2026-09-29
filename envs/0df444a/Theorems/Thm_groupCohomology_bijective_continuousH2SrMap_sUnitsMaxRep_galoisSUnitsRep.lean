-- Prove2me | Theorems.Thm_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
-- name    : groupCohomology.bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/830d529e-649a-5e70-ab29-bebb4528e9d1
-- title:
--   Change of S-unit coefficients is bijective on H²
-- statement:
--   Let $S$ be a finite set of rational primes and let $L$ be an intermediate field of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ (the Lean `AlgebraicClosure ℚ`) satisfying `IsUnramifiedOutside S`: $L$ is finite over $\mathbb{Q}$, and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ in the nonunits of $A$, the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$ over $\mathbb{Q}$ lies in the fixing subgroup of $L$. Two $\mathbb{Z}$-linear representations of $\Gamma_L =$ `L.fixingSubgroup` are compared: `sUnitsMaxRep S L`, the additive group of the subgroup `sUnitsMaxStable S L` of $\overline{\mathbb{Q}}^\times$ with its $\Gamma_L$-action, and the restriction along the inclusion $\Gamma_L \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of `galoisSUnitsRep S`, the additive group of those units $x$ of $\overline{\mathbb{Q}}$ such that both $x$ and $x^{-1}$ lie in every valuation subring of $\overline{\mathbb{Q}}$ lying over no prime of $S$. Given a $\mathbb{Z}$-linear map $\varphi$ between these two modules which on underlying units is the identity (hypothesis `hφv`, i.e. the unit underlying $\varphi(x)$ equals `sUnitsMaxRep.val S L x`) and is $\Gamma_L$-equivariant (hypothesis `hφ`), the conclusion is that the map `continuousH2SrMap` induced by $\varphi$ along the identity of $\Gamma_L$ — the map on the $S$-level degree-two cohomology `continuousH2Sr`, the quotient of `levelCocyclesSr₂` by the coboundaries contained in it, taken with respect to the inclusion $\Gamma_L \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ — is bijective.
--
--   Both sides are models of the second Galois cohomology group of the $S$-units of the maximal extension of $L$ unramified outside $S$, one built from units stable under $\Gamma_L$ inside levels unramified outside $S$, the other from the $S$-units of the full algebraic closure; the statement records that the natural change of coefficients identifies them. It is used by the results computing the $S$-level $H^2$ of `galoisSUnitsRep`: the vanishing criteria via restriction to levels and to $\mathbb{Q}(\sqrt{-1})$, and the bound on the torsion of this $H^2$ in terms of the number of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_GroupCohomology_GaloisSUnits
import Definitions.Def_NumberField_SUnitsMax

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory Module groupCohomology NumberField.LevelArith

theorem groupCohomology.bijective_continuousH2SrMap_sUnitsMaxRep_galoisSUnitsRep
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    (φ : sUnitsMaxRep S L →ₗ[ℤ] Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S))
    (hφv : ∀ x : sUnitsMaxRep S L,
      ((Additive.toMul (φ x) : ↥(galoisSUnits S)) : (AlgebraicClosure ℚ)ˣ) = sUnitsMaxRep.val S L x)
    (hφ : ∀ (g : ↥L.fixingSubgroup) (a : sUnitsMaxRep S L),
      φ ((sUnitsMaxRep S L).ρ g a) = (Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S)).ρ g (φ a)) :
    Function.Bijective
      (continuousH2SrMap (rH := L.fixingSubgroup.subtype) (rG := L.fixingSubgroup.subtype)
        (A := sUnitsMaxRep S L) (B := Rep.res L.fixingSubgroup.subtype (galoisSUnitsRep S))
        (MonoidHom.id ↥L.fixingSubgroup) (fun _ => rfl) S φ hφ) := by sorry
