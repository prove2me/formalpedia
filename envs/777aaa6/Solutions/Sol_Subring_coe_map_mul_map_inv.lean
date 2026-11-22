-- Prove2me | solution 1 for Subring.coe_map_mul_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:45:41.930064+00:00
-- url     : https://prove2.me/submissions/eea62618-db90-40cd-9562-13e58e76d59b

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Definitions.Def_BruhatTits_Utils_RingHom
import Theorems.Thm_GL_coe_map_mul_map_inv
attribute [local simp] GL.coe_map_mul_map_inv

set_option autoImplicit false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
variable {α : Type*} [DecidableEq α] [Fintype α]
variable {K : Type*} [CommRing K] (R : Subring K)
namespace Subring
theorem _root_.solution (g : GL α R) :
    g.val.map Subtype.val * g.val⁻¹.map Subtype.val = 1 :=
  GL.coe_map_mul_map_inv R.subtype g
end Subring
