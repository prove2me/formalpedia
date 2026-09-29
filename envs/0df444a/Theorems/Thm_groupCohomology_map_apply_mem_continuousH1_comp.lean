-- Prove2me | Theorems.Thm_groupCohomology_map_apply_mem_continuousH1_comp
-- name    : groupCohomology.map_apply_mem_continuousH1_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/c239e3e6-a903-5845-bbee-aa79aad6499e
-- title:
--   Functoriality preserves continuous degree-one classes
-- statement:
--   Let $k$ be a commutative ring and let $G$, $H$ be groups (all in one universe), let $r : G \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ be a group homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, let $\mathrm{loc} : H \to G$ be a group homomorphism, and let $M$ be a $k$-linear representation of $G$. Let $x$ be a class in $H^1(G, M)$ and assume $x \in$ `continuousH1 r M`, that is, $x$ lies in the image under the projection `H1π M` from one-cocycles to $H^1$ of the submodule `levelCocycles₁ r M` of one-cocycles that are of some finite level with respect to $r$. The conclusion is that the image of $x$ under the $k$-linear map underlying the degree-one functoriality morphism `map loc (𝟙 (Rep.res loc M)) 1`, associated with the homomorphism $\mathrm{loc}$ and the identity morphism of the restricted representation `Rep.res loc M`, belongs to `continuousH1 (r.comp loc) (Rep.res loc M)`: the image under `H1π (Rep.res loc M)` of `levelCocycles₁ (r.comp loc) (Rep.res loc M)`, the level condition now being taken with respect to the composite $r \circ \mathrm{loc} : H \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$.
--
--   This is the compatibility of the degree-one restriction (change-of-group) map with the continuity, i.e. local constancy, condition on cocycles: pulling back a continuous class along $\mathrm{loc}$ yields a continuous class for the composed Galois character. It is used in the Galois-cohomological bookkeeping for local conditions, for instance in the Greenberg–Wiles computations of unramified and arithmetic local terms and in the lemma on invariants of representations unipotent on inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_apply_mem_continuousH1_comp.lean

import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology
universe u

theorem groupCohomology.map_apply_mem_continuousH1_comp
    {k G H : Type u} [CommRing k] [Group G] [Group H]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (loc : H →* G)
    (M : Rep.{u} k G) (x : H1 M) (hx : x ∈ continuousH1 r M) :
    (map loc (𝟙 (Rep.res loc M)) 1).hom x ∈ continuousH1 (r.comp loc) (Rep.res loc M) := by sorry
