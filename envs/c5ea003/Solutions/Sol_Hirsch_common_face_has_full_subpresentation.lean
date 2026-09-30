-- Prove2me | solution 1 for Hirsch.common_face_has_full_subpresentation
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T02:57:01.676948+00:00
-- url     : https://prove2.me/submissions/9be43732-246e-456b-9c23-29b779fd3360

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch HirschCommonFace

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    CommonFaceHasSubpresentationAtMost a b u x n := by
  refine ⟨n, le_rfl, Function.Embedding.refl (Fin n), ?_⟩
  rfl

#print axioms solution
