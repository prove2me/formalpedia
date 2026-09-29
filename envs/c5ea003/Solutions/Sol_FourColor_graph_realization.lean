-- Prove2me | solution 1 for FourColor.graph_realization
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-28T00:29:03.7703+00:00
-- url     : https://prove2.me/submissions/11bb6975-6e61-4d3b-abb1-69049524c997
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_FourColor_plane_drawing_dart_rotation
import Theorems.Thm_FourColor_dart_rotation_face_realization

open FourColor
universe u

theorem solution :
    ∀ (V : Type u) [Finite V] (G : SimpleGraph V), IsPlanar G →
      ∃ (n : ℕ) (H : Hypermap n), H.Planar ∧ H.Plain ∧ Nonempty (FaceRepresentation G H) := by
  intro V _ G hG
  obtain ⟨R, hR⟩ := plane_drawing_dart_rotation V G hG
  exact dart_rotation_face_realization V G R hR
