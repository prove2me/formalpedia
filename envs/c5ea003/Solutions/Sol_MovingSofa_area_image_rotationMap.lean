-- Prove2me | solution 1 for MovingSofa.area_image_rotationMap
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-10-03T16:57:14.327553+00:00
-- url     : https://prove2.me/submissions/7b66c01e-80b9-4746-816f-ac74d923685f

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_MovingSofa_Basic
import Definitions.Def_MovingSofa_Geometry_Rotation
import Definitions.Def_MovingSofa_Classical_Area

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open MovingSofa.ClassicalResults

theorem solution (α : Real.Angle) (S : Set MovingSofa.Point) :
    MovingSofa.ClassicalResults.area (MovingSofa.rotationMap α '' S) =
      MovingSofa.ClassicalResults.area S := by
  have himg : MovingSofa.rotationMap α '' S =
      (EuclideanGeometry.o.rotation α).symm ⁻¹' S := by
    ext p
    simp only [MovingSofa.rotationMap, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨_, h, (EuclideanGeometry.o.rotation α).apply_symm_apply p⟩
  change (MeasureTheory.volume (MovingSofa.rotationMap α '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [himg]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (EuclideanGeometry.o.rotation α).symm
    (E := MovingSofa.Point) (F := MovingSofa.Point)).measure_preimage_emb
    ((EuclideanGeometry.o.rotation α).symm.toHomeomorph.measurableEmbedding) S
