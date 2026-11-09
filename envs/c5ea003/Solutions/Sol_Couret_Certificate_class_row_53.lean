-- Prove2me | solution 1 for Couret.Certificate.class_row_53
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:35:19.514083+00:00
-- url     : https://prove2.me/submissions/d9eb674d-90d3-4535-8467-b77aef90b57a

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate





theorem p2m_local_class_row_53 : ClassFacts 53 := by decide



end Certificate
end Couret

theorem solution : Couret.Certificate.ClassFacts
  (@OfNat.ofNat.{0} Couret.Certificate.ClassId (nat_lit 53)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) (nat_lit 53))) := @_root_.Couret.Certificate.p2m_local_class_row_53

