-- Prove2me | solution 1 for Couret.Certificate.class_row_83
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:36:52.552918+00:00
-- url     : https://prove2.me/submissions/cdd40ded-b498-436e-b281-5c43c591c918

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate







theorem p2m_local_class_row_83 : ClassFacts 83 := by decide

end Certificate
end Couret

theorem solution : Couret.Certificate.ClassFacts
  (@OfNat.ofNat.{0} Couret.Certificate.ClassId (nat_lit 83)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) (nat_lit 83))) := @_root_.Couret.Certificate.p2m_local_class_row_83

