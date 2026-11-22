-- Prove2me | solution 1 for Subtype.val_comp_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:41:40.875175+00:00
-- url     : https://prove2.me/submissions/01a405bb-8796-4d29-ab83-ed04b1e4deba

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
import Definitions.Def_BruhatTits_Utils_Subring
import Theorems.Thm_Subtype_val_comp_single
attribute [local simp] Subtype.val_comp_single

set_option autoImplicit false
universe uCompat vCompat wCompat
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
omit [DecidableEq ι]
namespace Subtype
theorem _root_.solution (v w : ι → A) :
    Subtype.val ∘ (v + w) = Subtype.val ∘ v + Subtype.val ∘ w := by
  ext j
  simp
end Subtype
