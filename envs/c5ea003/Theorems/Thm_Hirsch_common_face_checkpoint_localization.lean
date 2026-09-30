-- Prove2me | Theorems.Thm_Hirsch_common_face_checkpoint_localization
-- name    : Hirsch.common_face_checkpoint_localization
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:02:06.198983+00:00
-- url     : https://prove2.me/theorems/e366bb9e-ae22-4ae9-a08f-92bc712ccd41
-- title:
--   Common-face dimension bound for nonvertex checkpoints
-- statement:
--   The common-face dimension of two points, not necessarily vertices, is controlled by the number of inequalities together with the two endpoint nullities and the all-neutral rank defect of the displacement.
--
--   Let $P\subseteq\mathbb{R}^d$ be cut out by $n$ linear inequalities. For points $x,y$ write $h$ for the dimension of the common-direction space of rows tight at both, write $p$ (resp. $q$) for the corresponding nullity at $x$ (resp. $y$) alone, and write $\delta$ for
--   $$
--   (d-1)-\operatorname{rank}\{\,a_i:a_i\ne 0,\ \langle a_i,y-x\rangle=0\,\}.
--   $$
--   Then
--   $$
--   2h+d\le n+p+q+\delta+1.
--   $$
--   No feasibility, boundedness, irredundancy, or circuit hypothesis is used. When $x$ and $y$ are vertices of a circuit step, the already proved vertex localization $2h+d\le n+1$ is the special case $p=q=\delta=0$ up to the usual tight-row spanning. The extra terms are the correction needed for nonvertex checkpoints.
--
--   **Formalization Note** The Lean statement writes $p,q,\delta$ in the public `HirschCommonFace` vocabulary. Natural subtraction is truncated.
-- source:
--   Nonvertex extension of the proved vertex circuit localization Hirsch.row_circuit_common_face_dimension_bound. Rank-nullity for nested row-evaluation kernels; no literature-priority claim. Candidate inequality from prove2me-work draft PR #64, now given a standalone kernel-checked proof.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_checkpoint_localization
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    2 * HirschCommonFace.commonFaceDim a b x y + d ≤
      n + HirschCommonFace.commonFaceDim a b x x +
        HirschCommonFace.commonFaceDim a b y y +
        ((d - 1) -
          Module.finrank ℝ
            (HirschCommonFace.rowEvalMap a
              (Finset.univ.filter (fun i =>
                a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0))).range) + 1 := by sorry

end Hirsch
