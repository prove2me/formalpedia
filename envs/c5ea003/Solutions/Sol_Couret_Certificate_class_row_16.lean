-- Prove2me | solution 1 for Couret.Certificate.class_row_16
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:34:56.5333+00:00
-- url     : https://prove2.me/submissions/5b881c8f-3ae3-49fa-8c24-59aa9728dcce

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate



theorem p2m_local_class_row_16 : ClassFacts 16 := by decide





end Certificate
end Couret

theorem solution : Couret.Certificate.ClassFacts
  (@OfNat.ofNat.{0} Couret.Certificate.ClassId (nat_lit 16)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 101) (instOfNatNat (nat_lit 101)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))) (nat_lit 16))) := @_root_.Couret.Certificate.p2m_local_class_row_16

