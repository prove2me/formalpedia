-- Prove2me | Theorems.Thm_groupCohomology_Cores_cores_map_res_eq_index_smul
-- name    : groupCohomology.Cores.cores_map_res_eq_index_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/bf091371-3bd7-59f7-9abd-f6c63c218eb5
-- title:
--   Corestriction after restriction is multiplication by the index on H²
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ a $k$-linear representation of $G$, and $H \le G$ a subgroup of finite index. Let $\tau$ be a transversal of $H$ in the sense of the project structure `Cores.Transversal`: a section $\sigma \colon G/H \to G$ of the quotient map, so that $\sigma(q)$ lies in the coset $q$ for every $q$, normalised by $\sigma(1) = 1$. Let $x$ be a class in $H^2(G, A)$, in Mathlib's `H2` of the representation $A$. The assertion is that applying the corestriction $\tau$-cochain map `Cores.cores A τ` to the image of $x$ under Mathlib's restriction map in degree $2$, namely the map induced on $H^2$ by the inclusion $H \hookrightarrow G$ together with the identity of $\mathrm{Res}_H A$, returns $[G:H] \cdot x$, the $\mathbb{N}$-scalar multiple of $x$ by the index of $H$. Here `Cores.cores A τ` is the $k$-linear map $H^2(H, \mathrm{Res}_H A) \to H^2(G, A)$ obtained by transporting $H^2$ of the restricted representation to the quotient of inhomogeneous $2$-cocycles by coboundaries and descending the explicit $\tau$-indexed cochain-level corestriction formula `corCocycles₂ A τ` followed by the projection to $H^2(G,A)$. No normality assumption on $H$ is made.
--
--   This is the standard composition law $\mathrm{cor} \circ \mathrm{res} = [G:H]$ for the transfer (Eckmann corestriction) in group cohomology, here in degree $2$ and for the corestriction pinned by an explicit choice of transversal, so that later compatibilities can be stated against the same map. It is used in the local and Herbrand-quotient parts of the argument, where classes in $H^2$ are compared with their restrictions to subgroups of finite index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Cores_cores_map_res_eq_index_smul.lean

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.Cores.cores_map_res_eq_index_smul
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex] (τ : Cores.Transversal H) (x : H2 A) :
    Cores.cores A τ ((map H.subtype (𝟙 (Rep.res H.subtype A)) 2).hom x) = H.index • x := by sorry
