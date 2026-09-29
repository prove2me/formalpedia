-- Prove2me | Theorems.Thm_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
-- name    : groupCohomology.finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/fc3efe78-a43f-5ba9-a006-567cc961d73d
-- title:
--   Archimedean continuous H²: finite, of order at most two
-- statement:
--   Let $\Gamma$ denote the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $c =$ [`complexConjugation`](def/GaloisRep_ComplexConjugation.html#L30) be the automorphism of $\overline{\mathbb{Q}}$ obtained by restricting, via `AlgEquiv.restrictNormalHom`, the complex conjugation $\mathbb{C} \to \mathbb{C}$ viewed as a $\mathbb{Q}$-algebra automorphism, and let $\langle c\rangle$ be the subgroup of integer powers of $c$, which is the range of the inclusion `archimedeanLoc` of `archimedeanDecomposition` into $\Gamma$. For an arbitrary subgroup $U \le \Gamma$ and an arbitrary $g \in \Gamma$, put $D = U \cap g\langle c\rangle g^{-1}$, the image of $\langle c\rangle$ under conjugation by $g$ being taken via `MulAut.conj g`. Consider `continuousH2` for the inclusion $D \hookrightarrow \Gamma$ together with the restriction along $D \hookrightarrow \Gamma$ of the representation `Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)` attached to the action of $\Gamma$ on the unit group of $\overline{\mathbb{Q}}$; by definition this is the quotient of the group `levelCocycles₂` of $2$-cocycles of the appropriate level by its subgroup of those elements that are `levelCoboundaries₂`. The assertion is threefold: this quotient is finite; its cardinality is at most $2$; and if $gcg^{-1} \notin U$ then it is a subsingleton.
--
--   This is the archimedean local input to the counting of classes in continuous $H^2$ with values in $\overline{\mathbb{Q}}^\times$ over the places of a number field, encoding that the Brauer group of $\mathbb{R}$ has order $2$ and that of $\mathbb{C}$ is trivial, for the decomposition groups $U \cap g\langle c\rangle g^{-1}$ that index the archimedean places of the fixed field of $U$. Only the upper bound and the vanishing at complex places are asserted; it is used by [`groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one`](thm.html#groupCohomology.finprod_natCard_torsionBy_continuousH2_le_mul_natCard_torsionBy_continuousH2Sr_galoisSUnitsRep_of_sq_eq_neg_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two.lean

import Mathlib
import Definitions.Def_GaloisRep_ComplexConjugation
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology ExtCitation

theorem groupCohomology.finite_continuousH2_inf_map_conj_range_archimedeanLoc_and_natCard_le_two
    (U : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Finite (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) ∧
    Nat.card (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))) ≤ 2 ∧
    (g * complexConjugation * g⁻¹ ∉ U →
      Subsingleton (continuousH2 (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
        (Rep.res (U ⊓ (archimedeanLoc.range.map (MulAut.conj g).toMonoidHom)).subtype
          (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))))) := by sorry
