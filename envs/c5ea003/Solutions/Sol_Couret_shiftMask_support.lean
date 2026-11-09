-- Prove2me | solution 1 for Couret.shiftMask_support
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:00:57.0407+00:00
-- url     : https://prove2.me/submissions/f74dfd1e-ce1e-4248-b74c-c38841195410

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_shiftMaskOn_support
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret









theorem pythonAlphabet_complete : ∀ a : Code30, a ∈ pythonAlphabet := by decide































theorem p2m_local_shiftMask_support (g : Code30) (mask : Nat) (u : Code30) :
    maskSupport (shiftMask g mask) u ↔
      ∃ v, maskSupport mask v ∧ mul30 g v = u := by
  rw [shiftMask, shiftMaskOn_support]
  constructor
  · rintro ⟨v,_,hm,he⟩; exact ⟨v,hm,he⟩
  · rintro ⟨v,hm,he⟩; exact ⟨v,pythonAlphabet_complete v,hm,he⟩









































end Couret


theorem solution : ∀ (g : Couret.Code30) (mask : Nat) (u : Couret.Code30),
  Iff (Couret.maskSupport (Couret.shiftMask g mask) u)
    (@Exists.{1} Couret.Code30 fun v => And (Couret.maskSupport mask v) (@Eq.{1} Couret.Code30 (Couret.mul30 g v) u)) := @_root_.Couret.p2m_local_shiftMask_support

