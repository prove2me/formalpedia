-- Prove2me | Theorems.Thm_Hirsch_row_circuit_checkpoint_localization
-- name    : Hirsch.row_circuit_checkpoint_localization
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:19:10.378344+00:00
-- url     : https://prove2.me/theorems/af8c82a0-8a0e-4f28-bbd0-c5ac485d1faf
-- title:
--   Circuit steps from a vertex have vanishing source nullity and defect
-- statement:
--   A maximal row-circuit step leaving a vertex obeys checkpoint localization with source nullity and all-neutral defect both zero.
--
--   Let $P\subseteq\mathbb{R}^d$ be a bounded H-polytope, let $x$ be a vertex, and let $y-x$ be a row circuit. Write $h$ for the common-face dimension of $(x,y)$ and $q$ for the self common-face dimension of $y$. Then
--   $$
--   2h+d\le n+q+1.
--   $$
--   The source nullity vanishes because tight rows at a vertex span. The all-neutral defect vanishes because a circuit direction spans the kernel of the rows annihilating it. If $y$ is also a vertex then $q=0$ and one recovers the already proved bound $2h+d\le n+1$.
--
--   **Formalization Note** Boundedness is used only to rule out a lineality direction with empty row support.
-- source:
--   Specialization of Hirsch.common_face_checkpoint_localization to a row-circuit displacement leaving a vertex, using Hirsch.vertex_tight_rows_span and the elementary-vector property of circuits in a pointed bounded H-polytope.

import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem row_circuit_checkpoint_localization
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hx : x ∈ Set.extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (y - x)) :
    2 * HirschCommonFace.commonFaceDim a b x y + d ≤
      n + HirschCommonFace.commonFaceDim a b y y + 1 := by sorry

end Hirsch
