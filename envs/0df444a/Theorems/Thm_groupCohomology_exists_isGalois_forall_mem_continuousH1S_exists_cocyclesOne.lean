-- Prove2me | Theorems.Thm_groupCohomology_exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne
-- name    : groupCohomology.exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/e79384b5-179c-5860-8f5b-77af26ae871c
-- title:
--   A common unramified Galois splitting field for H¹_S
-- statement:
--   Let $k$ be a finite commutative ring, $S$ a finite set of rational primes, and $M$ an object of `Rep k Γ`, where $Γ = \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ is realised as the $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`; assume that the $k$-submodule `continuousH1S S M` of $H^1(Γ,M)$ — the image under the projection `H1π M` of the submodule `levelCocyclesS₁ S M` of $1$-cocycles — is a finite $k$-module. Then there exists an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$, together with the data making $F$ a number field and $F/\mathbb Q$ Galois, such that $F$ is unramified outside $S$ in the sense of [`IntermediateField.IsUnramifiedOutside`](def/GroupCohomology_ContinuousUnramified.html#L16), namely $F/\mathbb Q$ is finite-dimensional and for every prime $q \notin S$ and every valuation subring $A$ of $\overline{\mathbb Q}$ with $q$ a nonunit of $A$, the image in $Γ$ of the inertia subgroup of $A$ over $\mathbb Q$ (transported along the inclusion of the decomposition subgroup) lies in the fixing subgroup of $F$; and such that every class $x \in$ `continuousH1S S M` is of the form $x =$ `(H1π M).hom ny` for some $1$-cocycle $ny \in$ `cocycles₁ M` satisfying $ny(\gamma s) = ny(\gamma)$ for all $\gamma \in Γ$ and all $s$ in the fixing subgroup of $F$, and $ny(s) = 0$ for all such $s$.
--
--   This is the statement that, when the $S$-ramified first cohomology is finite over $k$, a single finite Galois extension of $\mathbb Q$ unramified outside $S$ serves simultaneously as a level (splitting field) for representing cocycles of all classes, the cocycles being inflated from $\operatorname{Gal}(F/\mathbb Q)$. It is used in the computations of Selmer-type groups and local restriction maps, being cited in the construction of classes with prescribed local behaviour away from $2$ and in the duality statement for the associated $Ш^1$/$Ш^2$ pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_isGalois_forall_mem_continuousH1S_exists_cocyclesOne
    {k : Type} [CommRing k] [Finite k] (S : Finset Nat.Primes) (M : Rep k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    [Module.Finite k ↥(continuousH1S S M)] :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F), F.IsUnramifiedOutside S ∧
      ∀ x : H1 M, x ∈ continuousH1S S M →
        ∃ ny : cocycles₁ M, (H1π M).hom ny = x ∧
          (∀ (γ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ny (γ * s) = ny γ) ∧
          (∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F.fixingSubgroup → ny s = 0) := by sorry
