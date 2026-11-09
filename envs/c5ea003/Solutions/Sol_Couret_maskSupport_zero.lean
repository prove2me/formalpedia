-- Prove2me | solution 1 for Couret.maskSupport_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:48:02.524168+00:00
-- url     : https://prove2.me/submissions/722e9718-ec3f-495e-8a60-9d10ca0d2bfa

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret























theorem p2m_local_maskSupport_zero (u : Code30) : ¬ maskSupport 0 u := by
  simp [maskSupport]



























































end Couret


theorem solution : ∀ (u : Couret.Code30), Not (Couret.maskSupport (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) u) := @_root_.Couret.p2m_local_maskSupport_zero

