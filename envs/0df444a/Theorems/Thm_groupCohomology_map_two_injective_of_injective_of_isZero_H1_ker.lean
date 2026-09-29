-- Prove2me | Theorems.Thm_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker
-- name    : groupCohomology.map_two_injective_of_injective_of_isZero_H1_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/369c2557-7632-53a4-9a26-4c38b541bc86
-- title:
--   Injectivity of inflation on H² when H¹ of the kernel vanishes
-- statement:
--   Let $G$ and $G'$ be finite groups, let $\pi\colon G'\to G$ be a surjective group homomorphism, let $C$ be a $\mathbb{Z}$-linear representation of $G$ and $C'$ one of $G'$, and let $j\colon \mathrm{Res}_\pi C\to C'$ be a morphism of representations of $G'$, where $\mathrm{Res}_\pi C$ is $C$ with $G'$ acting through $\pi$; thus the underlying $\mathbb{Z}$-linear map $j$ satisfies $j(\rho_C(\pi a)c)=\rho_{C'}(a)j(c)$ for all $a\in G'$, $c\in C$. Assume that $j$ is injective on underlying modules; that every $c'\in C'$ fixed by every element of $\ker\pi$ lies in the image of $j$; and that the degree-one group cohomology of the restriction of $C'$ along the inclusion $\ker\pi\hookrightarrow G'$, i.e. $H^1(\ker\pi, C')$, is a zero object. The conclusion is that the underlying map of the morphism $H^2(G,C)\to H^2(G',C')$ induced by the pair $(\pi, j)$, namely `groupCohomology.map π j 2`, is injective.
--
--   This is the injectivity (inflation) half of the inflation–restriction exact sequence in degree two, in the form in which the coefficient module upstairs has its $\ker\pi$-invariants captured by $j$ and $H^1$ of the kernel vanishes. It is used in the computation of fundamental classes of $S$-idèle class groups, via [`M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two`](thm.html#M4aHerbrand.exists_fundamentalClass_ideleClassGroup_map_eq_finrank_smul_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_two_injective_of_injective_of_isZero_H1_ker.lean

import Mathlib
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.map_two_injective_of_injective_of_isZero_H1_ker {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G']
    (π : G' →* G) (hπ : Function.Surjective π)
    (C : Rep ℤ G) (C' : Rep ℤ G') (j : Rep.res π C ⟶ C') (hj : Function.Injective j.hom)
    (hjN : ∀ c' : C', (∀ g' : G', g' ∈ π.ker → C'.ρ g' c' = c') → c' ∈ Set.range j.hom)
    (h1 : CategoryTheory.Limits.IsZero (groupCohomology (Rep.res π.ker.subtype C') 1)) :
    Function.Injective (groupCohomology.map π j 2).hom := by sorry
