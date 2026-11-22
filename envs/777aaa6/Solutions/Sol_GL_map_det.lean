-- Prove2me | solution 1 for GL.map_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:43:16.430427+00:00
-- url     : https://prove2.me/submissions/34de1c4f-8502-4871-9b61-03df8d6e3e0e

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_map_apply
import Theorems.Thm_GL_map_one
attribute [local simp] GL.map_apply
attribute [local simp] GL.map_one

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
namespace «GL»
theorem _root_.solution (g : GL α R) : Matrix.GeneralLinearGroup.det (GL.map f g) =
    Units.map f (Matrix.GeneralLinearGroup.det g) := by
  ext
  simp only [map, RingHom.mapMatrix_apply, Units.inv_eq_val_inv, Matrix.coe_units_inv,
    Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe]
  symm
  apply RingHom.map_det
end «GL»
