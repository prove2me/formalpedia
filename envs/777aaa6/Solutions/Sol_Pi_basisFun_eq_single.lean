-- Prove2me | solution 1 for Pi.basisFun_eq_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:03.323222+00:00
-- url     : https://prove2.me/submissions/9f690659-9ac0-4c5a-9bf4-d8d758761b77

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace Pi
theorem _root_.solution {ι : Type*} [Finite ι] [DecidableEq ι] {R : Type*}
    [Semiring R] (i : ι) : Pi.basisFun R ι i = Pi.single i 1 := by
  simp only [Pi.basisFun_apply]
end Pi
