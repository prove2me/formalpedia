-- Prove2me | Theorems.Thm_groupCohomology_map_resIhom_comp_ihom_map_counit_one_bijective
-- name    : groupCohomology.map_resIhom_comp_ihom_map_counit_one_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/590fd5cb-c2dd-592f-8ef3-e31b11d8796c
-- title:
--   Shapiro bijectivity for H¹(G,Hom(R,Coind Y))
-- statement:
--   Let $G$ be a group, $D \le G$ a subgroup, $R$ an object of $\mathrm{Rep}\,\mathbb{Z}\,G$ (a $\mathbb{Z}[G]$-module) and $Y$ an object of $\mathrm{Rep}\,\mathbb{Z}\,D$ (a $\mathbb{Z}[D]$-module). Consider the morphism of $\mathbb{Z}[D]$-modules obtained by composing, in diagrammatic order, [`Rep.resIhom`](def/GroupCohomology_RelationModuleRes.html#L39) along the inclusion $D \hookrightarrow G$ at the pair $(R, \mathrm{Coind}_{D}^{G} Y)$ — the map which is the identity on underlying carriers and identifies the restriction to $D$ of the internal hom $\mathrm{Hom}(R, \mathrm{Coind}_{D}^{G} Y)$ with the internal hom $\mathrm{Hom}(\mathrm{Res}\,R, \mathrm{Res}\,\mathrm{Coind}_{D}^{G} Y)$ of the restricted representations — with the image under the functor $\mathrm{Hom}(\mathrm{Res}\,R, -)$ of the component at $Y$ of the counit of Mathlib's restriction–coinduction adjunction `Rep.resCoindAdjunction`, i.e. post-composition with the evaluation of a coinduced function at $1$. Applying $H^{1}$-functoriality `groupCohomology.map` along $D \hookrightarrow G$ to this morphism in degree $1$ yields a homomorphism
--   $$H^{1}\bigl(G, \mathrm{Hom}(R, \mathrm{Coind}_{D}^{G} Y)\bigr) \longrightarrow H^{1}\bigl(D, \mathrm{Hom}(\mathrm{Res}\,R, Y)\bigr).$$
--   The assertion is that the underlying function of this homomorphism is bijective.
--
--   This is Shapiro's lemma in degree one, in the form adapted to the isomorphism $\mathrm{Hom}(R, \mathrm{Coind}_{D}^{G} Y) \cong \mathrm{Coind}_{D}^{G}\mathrm{Hom}(\mathrm{Res}\,R, Y)$ of $G$-modules, with the comparison map written explicitly as restriction to $D$ followed by evaluation at $1$ inside the internal hom. It feeds the construction of the nondegenerate pairing in [`groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two`](thm.html#groupCohomology.exists_sha1_dualTwist_sha2_pairing_nondegenerate_of_ne_two), where local cohomology at a place is compared with global cohomology of a coinduced module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_resIhom_comp_ihom_map_counit_one_bijective.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

theorem groupCohomology.map_resIhom_comp_ihom_map_counit_one_bijective
    {G : Type} [Group G] (D : Subgroup G) (R : Rep ℤ G) (Y : Rep ℤ ↥D) :
    Function.Bijective (groupCohomology.map D.subtype
      (Rep.resIhom D.subtype R (Rep.coind D.subtype Y) ≫
        (ihom (Rep.res D.subtype R)).map ((Rep.resCoindAdjunction ℤ D.subtype).counit.app Y)) 1).hom := by sorry
