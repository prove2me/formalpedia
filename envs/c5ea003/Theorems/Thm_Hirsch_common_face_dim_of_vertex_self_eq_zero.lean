-- Prove2me | Theorems.Thm_Hirsch_common_face_dim_of_vertex_self_eq_zero
-- name    : Hirsch.common_face_dim_of_vertex_self_eq_zero
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:11:17.409338+00:00
-- url     : https://prove2.me/theorems/4ac43e1d-ed08-4c6f-b65b-f81fd5fd9508
-- title:
--   A vertex has trivial self common-face dimension
-- statement:
--   At a vertex the common-face dimension of the vertex with itself is zero.
--
--   Let $v$ be an extreme point of an H-polytope $P=\{x:\langle a_i,x\rangle\le b_i\}$. The common-direction space of the pair $(v,v)$ is the kernel of all nonzero describing rows tight at $v$. Those rows already span the dual, so the kernel is trivial and
--   $$
--   \operatorname{dim} F(v,v)=0.
--   $$
--   No boundedness or irredundancy hypothesis is used.
--
--   **Formalization Note** This is the $p=0$ (or $q=0$) special case of checkpoint localization when an endpoint is a vertex.
-- source:
--   Immediate from Prove2Me theorem Hirsch.vertex_tight_rows_span: the nonzero tight rows at an extreme point span, so their evaluation kernel is zero. Used as the p=q=0 case of Hirsch.common_face_checkpoint_localization.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_dim_of_vertex_self_eq_zero
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b)) :
    HirschCommonFace.commonFaceDim a b v v = 0 := by sorry

end Hirsch
