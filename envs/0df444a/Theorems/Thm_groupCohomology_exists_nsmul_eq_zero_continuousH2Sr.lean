-- Prove2me | Theorems.Thm_groupCohomology_exists_nsmul_eq_zero_continuousH2Sr
-- name    : groupCohomology.exists_nsmul_eq_zero_continuousH2Sr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/af17e953-1f27-5b9f-84ea-e238eaf8840e
-- title:
--   Torsion of classes in the S-level continuous H²
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r : G \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a group homomorphism from $G$ to the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` (a level map), let $S$ be a finite set of rational primes, and let $M$ be a $k$-linear representation of $G$ (an object of `Rep k G` in universe $0$). Write $\mathrm{continuousH2Sr}\,r\,S\,M$ for the quotient of the submodule `levelCocyclesSr₂ r S M` of $2$-cochains — cocycles that are constant on cosets of the fixing subgroup, pulled back along $r$, of some finite subextension of $\overline{\mathbb{Q}}/\mathbb{Q}$ unramified outside $S$ — by the pullback along the inclusion of `levelCocyclesSr₂ r S M` of the submodule `levelCoboundariesSr₂ r S M`. The assertion is that every element $x$ of this quotient is torsion: there exists a natural number $n$ with $0 < n$ and $n \bullet x = 0$. No continuity, smoothness or finiteness hypothesis on $M$ or on $G$ is imposed, and the particular $n$ produced by the proof (the index of a level subgroup) is not recorded in the statement.
--
--   This is the cochain-level form, for the $S$-ramified continuous $H^2$ with level-constant inhomogeneous cochains, of the classical fact that the cohomology of a profinite group with discrete coefficients is torsion in positive degrees. It feeds the analysis of level-constant $2$-cocycles used when lifting a residual representation, being cited in the proof that a suitable level-constant class with trivial cyclotomic character is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_nsmul_eq_zero_continuousH2Sr.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_nsmul_eq_zero_continuousH2Sr
    {k : Type} [CommRing k] {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (x : continuousH2Sr r S M) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by sorry
