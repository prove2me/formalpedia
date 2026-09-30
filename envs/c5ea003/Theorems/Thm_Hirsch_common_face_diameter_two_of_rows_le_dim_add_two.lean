-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_two_of_rows_le_dim_add_two
-- name    : Hirsch.common_face_diameter_two_of_rows_le_dim_add_two
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T17:31:58.833386+00:00
-- url     : https://prove2.me/theorems/ca4c980f-86d7-4810-be9e-30e473b9dd70
-- title:
--   Every common carrier has diameter two at ambient row excess at most two
-- statement:
--   Let P={x in R^d : <a_i,x> <= b_i for i=1,...,n} be bounded and let u be any feasible point of P. If n<=d+2, then for every point v (not necessarily feasible or a vertex), the face of P cut out by all nonzero describing rows that are tight at both u and v has intrinsic padded vertex-edge graph diameter at most 2. Empty or lower-dimensional carriers, redundant rows, and zero-normal tautologies are allowed. The result is a low-excess carrier theorem, not a statement that arbitrary Polynomial Hirsch carriers have row excess at most two.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/d85e9ff15194bd413c5f7e71e6f1f10e2b98697c ; standalone Lean/Axiom gate Actions run 34628073766

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_common_face_geometry
open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

namespace Hirsch
theorem common_face_diameter_two_of_rows_le_dim_add_two
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Hpoly a b) (hrows : n ≤ d + 2) :
    DiamLE (HirschCommonFace.commonFace a b u v) 2 := by sorry
end Hirsch
