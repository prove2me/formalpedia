-- Prove2me | Theorems.Thm_groupCohomology_inhomogeneousCochains_d_d_apply
-- name    : groupCohomology.inhomogeneousCochains_d_d_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/90ca367e-7281-5ff6-a9b2-0a4f976bee59
-- title:
--   Pointwise vanishing of d∘ d on inhomogeneous cochains
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $A$ be a representation of $G$ over $k$ in the zeroth universe, i.e. an object of `Rep k G`. Fix a natural number $n$ and an inhomogeneous $n$-cochain $y$, that is, an arbitrary function from $(\mathrm{Fin}\ n \to G)$ to the underlying module of $A$. The differentials `inhomogeneousCochains.d A n` and `inhomogeneousCochains.d A (n+1)` of the inhomogeneous cochain complex are morphisms of $k$-modules from the $k$-module of $n$-cochains to that of $(n+1)$-cochains, and from $(n+1)$-cochains to $(n+2)$-cochains respectively; applying the underlying functions of these maps in turn, the assertion is that $d_{n+1}(d_n y) = 0$ as an element of the module of $(n+2)$-cochains, i.e. the zero function on $(\mathrm{Fin}\ (n+2) \to G)$. Thus the statement is the elementwise form of the identity $d\circ d = 0$ for the inhomogeneous cochains computing the group cohomology of $A$, with no hypothesis on $y$.
--
--   This is the usual fact that the inhomogeneous cochain differential squares to zero, rendered as an equality of cochains rather than as a composition of maps in a homological complex; in that shape it supplies the cocycle condition needed to produce classes in $H^{n+1}$. It is used in the construction of level-modifying cocycles in the arithmetic of $S$-ideles, in [`NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp`](thm.html#NumberField.LevelArith.exists_level_d_two_three_eq_of_sIdele_coboundary_of_smul_eq_of_dvd_natCard_decomp) and [`NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d`](thm.html#NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_inhomogeneousCochains_d_d_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_d_apply
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (y : (Fin n → G) → A) :
    (inhomogeneousCochains.d A (n + 1)).hom ((inhomogeneousCochains.d A n).hom y) = 0 := by sorry
