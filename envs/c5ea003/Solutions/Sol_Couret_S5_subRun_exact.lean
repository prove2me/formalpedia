-- Prove2me | solution 1 for Couret.S5.subRun_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:34.170316+00:00
-- url     : https://prove2.me/submissions/81bfabdc-7681-4638-b83d-837f445671bf

import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
import Std
import Theorems.Thm_Couret_S5_selectedSupport_snoc
import Theorems.Thm_Couret_maskSupport_or
import Theorems.Thm_Couret_maskSupport_singleton
import Theorems.Thm_Couret_maskSupport_zero
import Theorems.Thm_Couret_shiftMask_support
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5













theorem subStep_support (m : Nat) (g u : Code30) :
    maskSupport (subStep m g) u ↔
      maskSupport m u ∨ (∃ v, maskSupport m v ∧ mul30 g v = u) ∨ u = g := by
  simp only [subStep, maskSupport_or, shiftMask_support, maskSupport_singleton]
  exact or_assoc



theorem p2m_local_subRun_exact (w : Word Code30) (u : Code30) :
    maskSupport (subRun w) u ↔ selectedSupport w u := by
  induction w generalizing u with
  | empty =>
    constructor
    · exact fun h => False.elim (maskSupport_zero u h)
    · rintro ⟨s,h,_⟩; cases s; exact False.elim h
  | snoc w g ih =>
    rw [subRun,subStep_support,selectedSupport_snoc]
    simp only [ih]

end S5
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Couret.Code30) (u : Couret.Code30),
  Iff (Couret.maskSupport (Couret.S5.subRun w) u) (Couret.S5.selectedSupport w u) := @_root_.Couret.S5.p2m_local_subRun_exact

