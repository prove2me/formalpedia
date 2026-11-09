-- Prove2me | solution 1 for Couret.maskSupport_or
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:51.863144+00:00
-- url     : https://prove2.me/submissions/19aeee0d-1345-428a-ac07-c3277d068fb8

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret



























theorem p2m_local_maskSupport_or (a b : Nat) (u : Code30) :
    maskSupport (a ||| b) u ↔ maskSupport a u ∨ maskSupport b u := by
  simp [maskSupport, Nat.testBit_or, Bool.or_eq_true]























































end Couret


theorem solution : ∀ (a b : Nat) (u : Couret.Code30),
  Iff (Couret.maskSupport (@HOr.hOr.{0, 0, 0} Nat Nat Nat (@instHOrOfOrOp.{0} Nat Nat.instOrOp) a b) u)
    (Or (Couret.maskSupport a u) (Couret.maskSupport b u)) := @_root_.Couret.p2m_local_maskSupport_or

