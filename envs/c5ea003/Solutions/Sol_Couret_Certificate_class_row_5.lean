-- Prove2me | solution 1 for Couret.Certificate.class_row_5
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:35:24.273875+00:00
-- url     : https://prove2.me/submissions/98efa109-e5f2-40b3-9ba2-be45157a5a2b

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate






theorem p2m_local_class_row_5 : ClassFacts 5 := by decide


end Certificate
end Couret

theorem solution : Couret.Certificate.ClassFacts
  (@OfNat.ofNat.{0} Couret.Certificate.ClassId (nat_lit 5)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) (nat_lit 5))) := @_root_.Couret.Certificate.p2m_local_class_row_5

