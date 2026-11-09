-- Prove2me | solution 1 for Couret.mask_254_omits_only_residue_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:06:02.078525+00:00
-- url     : https://prove2.me/submissions/f92b6454-202c-451c-882c-c31ff4a5c550

import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
import Std
import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316

/-!
COU-87 S3. The bit order is the Python order 1,7,11,13,17,19,23,29,
which differs from the lexicographic C2 x C4 order. Natural masks are used
without machine overflow. No finite-state minimality is asserted here.
-/

namespace Couret













































































theorem p2m_local_mask_254_omits_only_residue_one : ∀ u : Code30,
    maskSupport 254 u ↔ residue30 u ≠ 1 := by decide





end Couret


theorem solution : ∀ (u : Couret.Code30),
  Iff (Couret.maskSupport (@OfNat.ofNat.{0} Nat (nat_lit 254) (instOfNatNat (nat_lit 254))) u)
    (@Ne.{1} Nat (Couret.residue30 u) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.p2m_local_mask_254_omits_only_residue_one

