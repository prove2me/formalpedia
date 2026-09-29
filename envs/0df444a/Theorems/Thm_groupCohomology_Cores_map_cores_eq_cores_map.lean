-- Prove2me | Theorems.Thm_groupCohomology_Cores_map_cores_eq_cores_map
-- name    : groupCohomology.Cores.map_cores_eq_cores_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/e1403f43-eab8-5762-bebf-98e96b28d925
-- title:
--   Naturality of the degree-2 corestriction in the coefficients
-- statement:
--   Fix a commutative ring $k$ and a group $G$, and let $A,B$ be representations of $G$ over $k$ (objects of `Rep k G` in the base universe) and $\varphi \colon A \to B$ a morphism of representations. Let $K \le G$ be a subgroup of finite index, and let $\tau$ be a transversal for $K$ in the sense of the project, i.e. a function $\sigma \colon G/K \to G$ together with the conditions that $\sigma(q)$ reduces to $q$ for every coset $q$ and that $\sigma$ sends the trivial coset to $1$. For such data, `Cores.cores A \tau` denotes the $k$-linear corestriction in degree $2$: it is obtained from the comparison isomorphism for degree-2 cohomology followed by the map on $2$-cocycles given by the transversal-indexed corestriction formula `corCocycles₂ A τ` and the projection `H2π` to cohomology, this composite being well defined because the corestriction of a coboundary projects to zero. The assertion is that for every class $z$ in the degree-2 cohomology of the restriction of $A$ to $K$, the image of `Cores.cores A τ z` under the map induced in degree $2$ by the identity of $G$ and $\varphi$ coincides with `Cores.cores B τ` applied to the image of $z$ under the map induced in degree $2$ by the identity of $K$ and the restriction of $\varphi$ to $K$.
--
--   This is the naturality of corestriction (the transfer) in the coefficient module, in degree $2$ and for the explicit transversal-based corestriction used in the project. It is invoked in the Herbrand-quotient computations, where corestricted degree-2 classes have to be pushed forward along coefficient maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Cores_map_cores_eq_cores_map.lean

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.Cores.map_cores_eq_cores_map
    {k G : Type} [CommRing k] [Group G] (A B : Rep.{0} k G) (φ : A ⟶ B)
    (K : Subgroup G) [K.FiniteIndex] (τ : Cores.Transversal K) (z : groupCohomology (Rep.res K.subtype A) 2) :
    (groupCohomology.map (MonoidHom.id G) φ 2).hom (Cores.cores A τ z) =
      Cores.cores B τ ((groupCohomology.map (MonoidHom.id ↥K) ((Rep.resFunctor K.subtype).map φ) 2).hom z) := by sorry
