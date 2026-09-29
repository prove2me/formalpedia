-- Prove2me | Theorems.Thm_groupCohomology_levelCoboundaries2_le_levelCocycles2
-- name    : groupCohomology.levelCoboundaries2_le_levelCocycles2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b103c0c2-05d5-50b7-b360-1e6469f679ef
-- title:
--   Level-constant coboundaries lie in level-constant 2-cocycles
-- statement:
--   Fix a commutative ring $k$ and a group $G$, a group homomorphism $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ into the automorphism group of the algebraic closure $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` of $\mathbb{Q}$, and a representation $M$ of $G$ over $k$ (an object of `Rep k G`). For an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ write $U_F = \{s \in G : r(s) \in F.\mathrm{fixingSubgroup}\}$ for the corresponding level subgroup of $G$. The hypothesis `hsm` is smoothness of $M$ for these levels: for every $m \in M$ there is an intermediate field $F$ with $F/\mathbb{Q}$ finite-dimensional such that $M.\rho(s)\,m = m$ for all $s \in U_F$. The conclusion is the inclusion of submodules $\mathrm{levelCoboundaries}_2(r, M) \le \mathrm{levelCocycles}_2(r, M)$: every coboundary of a level-constant inhomogeneous $1$-cochain (one invariant under right translation by some level subgroup $U_F$ with $F/\mathbb{Q}$ finite) is itself a level-constant inhomogeneous $2$-cocycle, i.e. invariant under right translation of both of its arguments by a single such level subgroup.
--
--   This is the compatibility needed for the continuous (level-constant) second cohomology group attached to a smooth representation of a group mapping to the absolute Galois group of $\mathbb{Q}$ to be formed literally as level-constant $2$-cocycles modulo coboundaries of level-constant $1$-cochains. It is used in the analysis of membership in the level coboundaries, in the verification that the coboundary of a level-constant $1$-cochain is a level-constant $2$-cocycle, and in the construction of a level-constant $2$-cocycle from a local-inverse witness for the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_levelCoboundaries2_le_levelCocycles2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem groupCohomology.levelCoboundaries2_le_levelCocycles2 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (M : Rep k G)
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m) :
    groupCohomology.levelCoboundaries₂ r M ≤ groupCohomology.levelCocycles₂ r M := by sorry
