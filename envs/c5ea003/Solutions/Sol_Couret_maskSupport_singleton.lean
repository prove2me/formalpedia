-- Prove2me | solution 1 for Couret.maskSupport_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:11.544932+00:00
-- url     : https://prove2.me/submissions/36c0cfa0-d050-4ca9-91df-53965bfb75f6

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret





theorem bitIndex30_injective : ∀ a b : Code30,
    bitIndex30 a = bitIndex30 b → a = b := by decide



















theorem p2m_local_maskSupport_singleton (a u : Code30) :
    maskSupport (singletonMask a) u ↔ u = a := by
  simp only [maskSupport, singletonMask, Nat.testBit_two_pow, decide_eq_true_eq]
  constructor
  · intro h; exact (bitIndex30_injective a u h).symm
  · intro h; rw [h]

























































end Couret


theorem solution : ∀ (a u : Couret.Code30), Iff (Couret.maskSupport (Couret.singletonMask a) u) (@Eq.{1} Couret.Code30 u a) := @_root_.Couret.p2m_local_maskSupport_singleton

