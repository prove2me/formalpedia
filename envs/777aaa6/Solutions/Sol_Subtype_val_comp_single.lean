-- Prove2me | solution 1 for Subtype.val_comp_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:40:53.524651+00:00
-- url     : https://prove2.me/submissions/720e4c09-014a-4ff3-887a-8b73a9046218

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
import Definitions.Def_BruhatTits_Utils_Subring

set_option autoImplicit false
universe uCompat vCompat wCompat
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
namespace Subtype
theorem _root_.solution (i : ι) (a : A) :
    Subtype.val ∘ Pi.single i a = Pi.single i a := by
  ext j
  by_cases h : i = j
  all_goals aesop
end Subtype
