-- Prove2me | Theorems.Thm_groupCohomology_IsGradedCupProduct_unique
-- name    : groupCohomology.IsGradedCupProduct.unique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/4f1fb83c-ecd8-5174-9fd9-f566a3939cae
-- title:
--   Uniqueness of a graded cup product on group cohomology
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), and let $A$ and $B$ be $k$-linear representations of $G$. A `GradedCupFamily A B` is a family assigning to each pair of natural numbers $p,q$ a $k$-bilinear map $H^p(G,A) \times H^q(G,B) \to H^{p+q}(G, A \otimes B)$, realised as a $k$-linear map from $H^p(G,A)$ into the space of $k$-linear maps from $H^q(G,B)$ to $H^{p+q}(G,A\otimes B)$ in the inhomogeneous-cochain model. Given two such families $\cup$ and $\cup'$, each satisfying the predicate `IsGradedCupProduct`, i.e. for all $p,q$, every cocycle $x$ in degree $p$ for $A$ and every cocycle $y$ in degree $q$ for $B$, and every proof that the inhomogeneous differential in degree $p+q$ annihilates the cochain $\mathrm{cochainCup}\,A\,B\,p\,q$ applied to the underlying cochains of $x$ and $y$ (the explicit cochain-level cup product, whose value at $\sigma : \mathrm{Fin}(p+q) \to G$ is the tensor of the first cochain evaluated at the initial segment of $\sigma$ with the translate by $B.\rho$ of the partial product of that segment of the second cochain evaluated at the final segment), the family carries the classes of $x$ and $y$ to the class of that cochain regarded as a cocycle, the conclusion is $\cup = \cup'$, an equality of families.
--
--   This is the uniqueness half of the construction of the cup product $H^p(G,A) \otimes H^q(G,B) \to H^{p+q}(G,A \otimes B)$ in the inhomogeneous-cochain model: the defining compatibility with the explicit cochain-level product determines the family on cohomology completely. It is used in the construction of the Tate cup product, via [`Rep.exists_isTateCupProduct`](thm.html#Rep.exists_isTateCupProduct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_IsGradedCupProduct_unique.lean

import Mathlib
import Definitions.Def_GroupCohomology_CochainCup
import Definitions.Def_GroupCohomology_IsGradedCupProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory groupCohomology

theorem groupCohomology.IsGradedCupProduct.unique {k G : Type u} [CommRing k] [Group G] (A B : Rep.{u} k G)
    (cup cup' : groupCohomology.GradedCupFamily A B)
    (h : groupCohomology.IsGradedCupProduct A B cup) (h' : groupCohomology.IsGradedCupProduct A B cup') : cup = cup' := by sorry
