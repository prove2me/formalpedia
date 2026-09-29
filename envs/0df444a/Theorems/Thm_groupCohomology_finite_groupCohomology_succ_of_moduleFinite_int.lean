-- Prove2me | Theorems.Thm_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int
-- name    : groupCohomology.finite_groupCohomology_succ_of_moduleFinite_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/0e1ee0d4-367c-5e1d-95d4-cdfdb8c01b36
-- title:
--   Finiteness of Hⁿ⁺¹(G,L) for finite G and L finitely generated
-- statement:
--   Let $G$ be a finite group and let $L$ be an object of `Rep ℤ G`, that is, a $\mathbb{Z}$-linear representation of $G$, whose underlying $\mathbb{Z}$-module is finitely generated. Then for every natural number $n$, the group cohomology `groupCohomology L (n + 1)`, i.e. $H^{n+1}(G,L)$ computed by Mathlib's complex of inhomogeneous cochains, is a finite type. Note that the degree is constrained to be a successor: nothing is asserted about $H^0(G,L) = L^G$, which is in general infinite. The hypotheses on $G$ are finiteness and the group structure only, with no further conditions on $L$ beyond finite generation over $\mathbb{Z}$ of the module underlying the representation.
--
--   This is the standard finiteness statement for the higher cohomology of a finite group acting on a finitely generated abelian group: such cohomology is finitely generated and annihilated by $|G|$, hence finite. It serves as the finiteness input for Tate cohomology and Herbrand quotients of lattices, and is cited by [`Rep.finite_H1_ihom_relationModuleInt`](thm.html#Rep.finite_H1_ihom_relationModuleInt) and [`Rep.finite_tateCohomology_of_moduleFinite`](thm.html#Rep.finite_tateCohomology_of_moduleFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_groupCohomology_succ_of_moduleFinite_int.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology

theorem groupCohomology.finite_groupCohomology_succ_of_moduleFinite_int {G : Type} [Group G] [Finite G]
    (L : Rep ℤ G) [Module.Finite ℤ L] (n : ℕ) :
    Finite (groupCohomology L (n + 1)) := by sorry
