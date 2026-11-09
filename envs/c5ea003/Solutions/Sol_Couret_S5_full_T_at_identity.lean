-- Prove2me | solution 1 for Couret.S5.full_T_at_identity
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:36.793951+00:00
-- url     : https://prove2.me/submissions/71c7dd11-f4f5-4678-83d4-4377ff6ee9d6

import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
import Std
import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5




































theorem p2m_local_full_T_at_identity : (pairList (0,0) 255).length = 6 := by decide +kernel

end S5
end Couret

theorem solution : @Eq.{1} Nat
  (@List.length.{0} (Prod.{0, 0} Nat Nat)
    (Couret.S5.pairList
      (@Prod.mk.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0))))
      (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))))
  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) := @_root_.Couret.S5.p2m_local_full_T_at_identity

