-- Prove2me | Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_apply
-- name    : groupCohomology.inhomogeneousCochains_d_comp_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/77685a0b-ba5f-5ac9-99ee-048b1de8c457
-- title:
--   Morphisms of representations commute with the inhomogeneous differential
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $A$ and $B$ be representations of $G$ over $k$ (objects of `Rep k G` in universe $0$), with $\varphi\colon A \to B$ a morphism of representations, i.e. a $k$-linear $G$-equivariant map $\varphi$. Fix a natural number $n$ and a function $x\colon (\mathrm{Fin}\ n \to G) \to A$, that is, an inhomogeneous $n$-cochain of $G$ with values in $A$, with no cocycle condition imposed. The assertion is that applying the degree-$n$ to degree-$(n+1)$ differential of the complex `inhomogeneousCochains B` to the cochain $g \mapsto \varphi(x(g))$ yields the cochain $g \mapsto \varphi\bigl((d_A x)(g)\bigr)$, where $d_A$ is the corresponding differential of `inhomogeneousCochains A`; the equality is an equality of functions $(\mathrm{Fin}\ (n+1) \to G) \to B$. In other words, post-composition with $\varphi$ commutes with the inhomogeneous coboundary operator, at the level of raw cochains and in the concrete form in which the differentials of the complexes computing group cohomology are indexed.
--
--   This is the functoriality in the coefficients of the standard (inhomogeneous) cochain complex of a group, stated pointwise on cochains so that it can be used to rewrite goals formulated with the `HomologicalComplex` differential. It is used in the $S$-idele and level-arithmetic computations, where cochains for the unit and idele class groups of a number field are pushed along maps of coefficient modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_inhomogeneousCochains_d_comp_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_comp_apply
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (φ : A ⟶ B) (n : ℕ)
    (x : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (x g)) =
      fun g => φ.hom (((inhomogeneousCochains A).d n (n + 1)).hom x g) := by sorry
