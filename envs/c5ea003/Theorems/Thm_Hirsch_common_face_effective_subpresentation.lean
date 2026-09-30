-- Prove2me | Theorems.Thm_Hirsch_common_face_effective_subpresentation
-- name    : Hirsch.common_face_effective_subpresentation
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T03:24:17.844852+00:00
-- url     : https://prove2.me/theorems/79ccb375-2dd9-49e6-ab30-b04bcf1ff119
-- title:
--   Common-face coordinates have an equivalent nonzero-row subpresentation
-- statement:
--   If the first endpoint is feasible, the common-face coordinate polytope admits an equivalent subpresentation using only the nonzero restricted rows.
--
--   The origin of those coordinates is the first endpoint. Feasibility of that point forces every zero restricted row to be a tautology $0\le B_i$, so those rows may be dropped without changing the H-polytope. The resulting row count is `commonFaceEffectiveCount`. This bounds the least equivalent original-row count $M_{\min}$ from above. It does not identify $M_{\min}$ with the number of geometric facets.
--
--   **Formalization Note** The embedding enumerates the effective index Finset.
-- source:
--   Public fragment of the genuine-facet program: an equivalent subpresentation on the nonzero restricted rows. Does not identify that count with geometric facets.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_effective_subpresentation
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    HirschCommonFace.CommonFaceHasSubpresentationAtMost a b u x
      (HirschCommonFace.commonFaceEffectiveCount a b u x) := by sorry

end Hirsch
