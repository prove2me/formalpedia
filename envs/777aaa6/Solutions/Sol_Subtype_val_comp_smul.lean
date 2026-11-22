-- Prove2me | solution 1 for Subtype.val_comp_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:42:27.53018+00:00
-- url     : https://prove2.me/submissions/08511963-e65f-4503-8818-d2113ab4e734

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
import Definitions.Def_BruhatTits_Utils_Subring
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_add

set_option autoImplicit false
universe uCompat vCompat wCompat
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
omit [DecidableEq ι]
namespace Subtype
theorem _root_.solution (a : A) (v : ι → A) :
    Subtype.val ∘ (a • v) = a • Subtype.val ∘ v := by
  ext j
  simp
  rfl
end Subtype
