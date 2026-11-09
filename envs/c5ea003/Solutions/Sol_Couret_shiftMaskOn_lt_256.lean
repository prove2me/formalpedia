-- Prove2me | solution 1 for Couret.shiftMaskOn_lt_256
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:04.072995+00:00
-- url     : https://prove2.me/submissions/9b005f8c-4de0-48e8-b3a1-a948131aa7f9

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Theorems.Thm_Couret_singletonMask_lt_256
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret





































theorem p2m_local_shiftMaskOn_lt_256 (g : Code30) (mask : Nat) (letters : List Code30) :
    shiftMaskOn g mask letters < 256 := by
  induction letters with
  | nil => change 0 < 256; decide
  | cons a rest ih =>
    change ((if maskSupport mask a then singletonMask (mul30 g a) else 0) |||
      shiftMaskOn g mask rest) < 2^8
    apply Nat.or_lt_two_pow
    · split
      · exact singletonMask_lt_256 _
      · decide
    · exact ih













































end Couret


theorem solution : ∀ (g : Couret.Code30) (mask : Nat) (letters : List.{0} Couret.Code30),
  @LT.lt.{0} Nat instLTNat (Couret.shiftMaskOn g mask letters)
    (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) := @_root_.Couret.p2m_local_shiftMaskOn_lt_256

