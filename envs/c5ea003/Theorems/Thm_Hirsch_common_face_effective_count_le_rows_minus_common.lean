-- Prove2me | Theorems.Thm_Hirsch_common_face_effective_count_le_rows_minus_common
-- name    : Hirsch.common_face_effective_count_le_rows_minus_common
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T11:25:27.279481+00:00
-- url     : https://prove2.me/theorems/be716434-50fa-4b32-a13a-71c3ae2caa4b
-- title:
--   Common rows do not contribute effective common-face inequalities
-- statement:
--   Every nonzero row active at both defining points becomes a zero normal after restriction to their common-direction space. Therefore common rows and effective restricted rows are disjoint, and the effective row count is at most the total number of describing rows minus the number of common rows.
-- source:
--   Verified effective-row count lemma from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #33.

import Definitions.Def_Hirsch_common_face_geometry

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem common_face_effective_count_le_rows_minus_common
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    HirschCommonFace.commonFaceEffectiveCount a b p q ≤
      n - (HirschCommonFace.commonSourceRows a b p q).card := by sorry

end Hirsch
