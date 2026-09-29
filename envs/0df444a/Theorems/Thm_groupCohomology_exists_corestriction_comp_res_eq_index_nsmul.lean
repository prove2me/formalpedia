-- Prove2me | Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
-- name    : groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/4ff91d40-434c-5513-ba28-c967e3617fdc
-- title:
--   Existence of corestriction with corcircres=[G:H]
-- statement:
--   Let $G$ be a group, let $H \le G$ be a subgroup of finite index, let $M$ be a $\mathbb{Z}$-linear representation of $G$ (an object of `Rep ℤ G`), and let $n$ be a natural number. Write $\mathrm{Res}_H M$ for the representation of $H$ obtained from $M$ by restricting along the inclusion $H \hookrightarrow G$. The assertion is that there exists an additive homomorphism $\mathrm{cor} \colon H^n(H, \mathrm{Res}_H M) \to H^n(G, M)$ between the underlying additive groups of the group cohomology modules such that for every $x \in H^n(G, M)$ one has $\mathrm{cor}(\mathrm{res}\,x) = [G:H] \cdot x$, where $\mathrm{res}$ is the map on cohomology induced by functoriality from the pair consisting of the inclusion $H \hookrightarrow G$ and the identity morphism of $\mathrm{Res}_H M$, $[G:H]$ is the index of $H$ as a natural number, and $\cdot$ is the iterated-addition action of $\mathbb{N}$. The statement is purely existential: no further property of $\mathrm{cor}$ is asserted, in particular no formula for $\mathrm{res} \circ \mathrm{cor}$, no compatibility with the cup product, and no uniqueness.
--
--   This is the existence of the corestriction (transfer) map in group cohomology for a subgroup of finite index, together with the single relation $\mathrm{cor} \circ \mathrm{res} = [G:H]$ that makes $p$-primary statements about $H^n(G,M)$ checkable on a $p$-Sylow subgroup. It is used in the Herbrand-quotient and idèle-class arguments of the project, for instance in [`M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup`](thm.html#M4aHerbrand.finsum_div_natCard_decomp_eq_zero_of_isPGroup) and [`M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero`](thm.html#M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.exists_corestriction_comp_res_eq_index_nsmul
    {G : Type} [Group G] (H : Subgroup G) [H.FiniteIndex] (M : Rep ℤ G) (n : ℕ) :
    ∃ cor : groupCohomology (Rep.res H.subtype M) n →+ groupCohomology M n,
      ∀ x : groupCohomology M n,
        cor ((groupCohomology.map H.subtype (𝟙 (Rep.res H.subtype M)) n).hom x) = H.index • x := by sorry
