-- Prove2me | solution 1 for Couret.S5.subRun_bound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:22.443995+00:00
-- url     : https://prove2.me/submissions/3f9cb9e2-26fb-4bd6-a51a-cb2ebbcdb451

import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
import Std
import Theorems.Thm_Couret_shiftMaskOn_lt_256
import Theorems.Thm_Couret_singletonMask_lt_256
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5









theorem subStep_bound (m : Nat) (hm : m < 256) (g : Code30) : subStep m g < 256 := by
  change (m ||| shiftMask g m ||| singletonMask g) < 2^8
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow hm (shiftMaskOn_lt_256 g m pythonAlphabet)) (singletonMask_lt_256 g)

theorem p2m_local_subRun_bound (w : Word Code30) : subRun w < 256 := by
  induction w with
  | empty => change 0 < 256; decide
  | snoc w g ih => exact subStep_bound _ ih g







end S5
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Couret.Code30),
  @LT.lt.{0} Nat instLTNat (Couret.S5.subRun w) (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) := @_root_.Couret.S5.p2m_local_subRun_bound

