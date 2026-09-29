-- Prove2me | Theorems.Thm_groupCohomology_bijective_map_top_subtype
-- name    : groupCohomology.bijective_map_top_subtype
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/daa1cdf9-27ad-5934-aff1-f6e090eea8b1
-- title:
--   Restriction to the top subgroup is bijective on cohomology
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both carried by types in the lowest universe), let $A$ be an object of `Rep k G`, i.e. a $k$-linear representation of $G$, and let $n$ be a natural number. Consider the inclusion homomorphism `(⊤ : Subgroup G).subtype` of the top subgroup $\top \le G$ into $G$, and the identity morphism of the restricted representation `Rep.res (⊤ : Subgroup G).subtype A`, which is an admissible coefficient morphism for that homomorphism. The functoriality map `groupCohomology.map` then produces a morphism of $k$-modules from $H^n(G, A)$ to $H^n(\top, \operatorname{Res}_{\top} A)$, namely restriction of cochains along $\top \hookrightarrow G$ with no change of coefficients. The assertion is that the underlying $k$-linear map of this morphism, obtained by `.hom`, is bijective as a function: restriction along the inclusion of the top subgroup is an isomorphism on $n$-th group cohomology for every $n$ and every coefficient representation.
--
--   This is the degenerate case of the restriction map in group cohomology, for the subgroup $\top \le G$, along which $\top \to G$ is an isomorphism of groups. It serves as a transport device: results proved for an arbitrary subgroup $S \le G$ with coefficients $\operatorname{Res}_S A$ can be specialised at $S = \top$ and read back as statements about $G$ itself; it is used in this form in the Herbrand-quotient computations and in the local fundamental class arguments for number fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_bijective_map_top_subtype.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

theorem groupCohomology.bijective_map_top_subtype {k G : Type} [CommRing k] [Group G] (A : Rep k G) (n : ℕ) :
    Function.Bijective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom := by sorry
