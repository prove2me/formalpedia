-- Prove2me | solution 1 for Couret.Certificate.class_row_61
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:36:31.529067+00:00
-- url     : https://prove2.me/submissions/8b9213e0-9ae2-46b9-a00d-51ea9eeaa7bc

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate






theorem p2m_local_class_row_61 : ClassFacts 61 := by decide


end Certificate
end Couret

theorem solution : Couret.Certificate.ClassFacts
  (@OfNat.ofNat.{0} Couret.Certificate.ClassId (nat_lit 61)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) (nat_lit 61))) := @_root_.Couret.Certificate.p2m_local_class_row_61

