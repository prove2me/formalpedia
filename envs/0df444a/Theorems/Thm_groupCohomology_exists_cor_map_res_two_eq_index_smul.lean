-- Prove2me | Theorems.Thm_groupCohomology_exists_cor_map_res_two_eq_index_smul
-- name    : groupCohomology.exists_cor_map_res_two_eq_index_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/f5ca65c8-24a0-5e8e-a95f-7e4e14ed643e
-- title:
--   Existence of corestriction on H² with corcircres=[G:S]
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $X$ a representation of $G$ over $k$ (an object of `Rep k G`), and $S \le G$ a subgroup whose index is finite (the typeclass `S.FiniteIndex`). The assertion is that there exists a $k$-linear map $$\mathrm{cor}\colon H^2(S, X|_S) \longrightarrow H^2(G, X),$$ from the degree-$2$ group cohomology of the restricted representation `Rep.res S.subtype X` to the degree-$2$ group cohomology of $X$, such that for every class $x \in H^2(G, X)$ one has $\mathrm{cor}(\mathrm{res}(x)) = [G:S] \cdot x$, where $\mathrm{res}$ is the underlying map of the morphism `groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2` induced in degree $2$ by the inclusion $S \hookrightarrow G$ together with the identity on $X|_S$, and $[G:S]$ is `S.index`, acting by the natural number scalar action. Only existence of such a map is asserted: no compatibility, functoriality or naturality property of $\mathrm{cor}$ beyond the displayed identity is part of the conclusion, and $\mathrm{cor}$ is not required to be canonical.
--
--   This is the degree-two case of the corestriction (transfer) map in group cohomology together with the identity $\mathrm{cor}\circ\mathrm{res} = [G:S]$, packaged in existence form, which is all that is needed to deduce that restriction is injective on $p$-primary parts when $p \nmid [G:S]$ and to run reductions to Sylow subgroups. It is used in the construction of fundamental classes for the idèle class group and in the $p$-group step of the level-arithmetic computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_cor_map_res_two_eq_index_smul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology Rep

theorem groupCohomology.exists_cor_map_res_two_eq_index_smul
    {k G : Type} [CommRing k] [Group G] (X : Rep k G) (S : Subgroup G) [S.FiniteIndex] :
    ∃ cor : groupCohomology (Rep.res S.subtype X) 2 →ₗ[k] groupCohomology X 2,
      ∀ x : groupCohomology X 2,
        cor ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype X)) 2).hom x) = S.index • x := by sorry
