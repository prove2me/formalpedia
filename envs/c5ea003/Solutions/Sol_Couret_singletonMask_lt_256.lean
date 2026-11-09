-- Prove2me | solution 1 for Couret.singletonMask_lt_256
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:00:56.769239+00:00
-- url     : https://prove2.me/submissions/f75b09ba-0a08-42b2-979f-2924b64036b9

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret





























theorem p2m_local_singletonMask_lt_256 : ∀ u : Code30, singletonMask u < 256 := by decide





















































end Couret


theorem solution : ∀ (u : Couret.Code30),
  @LT.lt.{0} Nat instLTNat (Couret.singletonMask u) (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) := @_root_.Couret.p2m_local_singletonMask_lt_256

