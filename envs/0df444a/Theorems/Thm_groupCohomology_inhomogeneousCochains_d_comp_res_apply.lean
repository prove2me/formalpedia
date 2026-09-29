-- Prove2me | Theorems.Thm_groupCohomology_inhomogeneousCochains_d_comp_res_apply
-- name    : groupCohomology.inhomogeneousCochains_d_comp_res_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b94be4a2-c009-5a59-be8a-84dddcf820b2
-- title:
--   Equivariant maps commute with the inhomogeneous coboundary
-- statement:
--   Let $k$ be a commutative ring, let $G$ and $H$ be groups, let $A$ be a $k$-linear representation of $G$ and let $B$ be a $k$-linear representation of $H$ (both in `Rep.{0}`). Let $f\colon H\to G$ be a group homomorphism and let $T\colon A\to B$ be a homomorphism of the underlying additive groups which is equivariant along $f$, in the sense that $T(A.\rho(f(h))\,a) = B.\rho(h)\,(T(a))$ for all $h\in H$ and $a\in A$; note that $T$ is required to be additive only, not $k$-linear. Let $n$ be a natural number and let $x\colon (\mathrm{Fin}\,n\to G)\to A$ be an inhomogeneous $n$-cochain of $G$ with values in $A$. The conclusion is an equality of inhomogeneous $(n+1)$-cochains of $H$ with values in $B$: applying the differential $d^{n}$ of `inhomogeneousCochains B` (as a map of underlying modules) to the cochain $g\mapsto T(x(f\circ g))$ yields the cochain $g\mapsto T\big((d^{n}x)(f\circ g)\big)$, where $d^{n}$ on the right is the differential of `inhomogeneousCochains A`.
--
--   This is the cochain-level functoriality of inhomogeneous cochains in the pair consisting of a group and a module — the computation underlying restriction and inflation maps in group cohomology — stated for an additive map with an explicit equivariance hypothesis rather than for a morphism of representations out of a restricted representation. It is used in the level-arithmetic results [`NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d`](thm.html#NumberField.LevelArith.exists_level_sUnitsRep_val_d_eq_of_sIdele_coboundary_of_map_eq_add_d) and [`NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le`](thm.html#NumberField.LevelArith.exists_smul_eq_smul_add_d_add_diag_of_sIdele_coboundary_of_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_inhomogeneousCochains_d_comp_res_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_comp_res_apply
    {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k G} {B : Rep.{0} k H}
    (f : H →* G) (T : A →+ B) (hT : ∀ (h : H) (a : A), T (A.ρ (f h) a) = B.ρ h (T a)) (n : ℕ)
    (x : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => T (x (f ∘ g))) =
      fun g => T (((inhomogeneousCochains A).d n (n + 1)).hom x (f ∘ g)) := by sorry
