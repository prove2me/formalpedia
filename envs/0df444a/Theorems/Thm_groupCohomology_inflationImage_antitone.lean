-- Prove2me | Theorems.Thm_groupCohomology_inflationImage_antitone
-- name    : groupCohomology.inflationImage_antitone
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/e6f42c58-d9d2-51f4-be31-22c8a9f389e8
-- title:
--   Antitonicity of the inflation image in the subgroup
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $M$ a representation of $G$ over $k$, i.e. an object of `Rep k G`. For a normal subgroup $S \le G$, `inflationImage M S` is the $k$-submodule of $H^1(G,M)$ given by the range of the linear map underlying `inflation M S`, which is the map on first group cohomology induced by the quotient homomorphism $G \to G/S$ together with the morphism of representations obtained from the factorisation of $\rho_M$ through the $S$-invariants; that is, it is the image of the inflation map $H^1(G/S, M^S) \to H^1(G,M)$. The theorem asserts: for normal subgroups $S, T$ of $G$ with $S \le T$, one has the inclusion of submodules of $H^1(G,M)$
--   $$\operatorname{im}\bigl(H^1(G/T, M^T) \to H^1(G,M)\bigr) \;\le\; \operatorname{im}\bigl(H^1(G/S, M^S) \to H^1(G,M)\bigr),$$
--   so that the assignment $S \mapsto$ `inflationImage M S` is antitone in the normal subgroup $S$.
--
--   This is the compatibility of inflation with passage to a smaller normal subgroup, in the form of an inclusion of images in $H^1(G,M)$; it is the directedness statement underlying the description of the locally constant (respectively unramified) classes as the union of the inflation images over a family of normal subgroups closed under intersection. It is used in the computations of ranks of spaces of locally constant and unramified continuous classes and in the study of norm maps on representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_inflationImage_antitone.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.inflationImage_antitone {k : Type u} [CommRing k] {G : Type u} [Group G] (M : Rep k G) {S T : Subgroup G} [S.Normal] [T.Normal]
    (hST : S ≤ T) : inflationImage M T ≤ inflationImage M S := by sorry
