-- Prove2me | solution 1 for Subring.coe_map_inv_mul_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:46:14.628941+00:00
-- url     : https://prove2.me/submissions/ab99eec5-8389-4d9b-a695-5ef0b42d23b9

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_coe_map_inv_mul_map
attribute [local simp] GL.coe_map_inv_mul_map

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {K : Type*} [CommRing K] (R : Subring K)
namespace Subring
theorem _root_.solution (g : GL α R) :
    g.val⁻¹.map Subtype.val * g.val.map Subtype.val = 1 :=
  GL.coe_map_inv_mul_map R.subtype g
end Subring
