-- Prove2me | solution 1 for Couret.Certificate.state_row_18
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:22:26.04374+00:00
-- url     : https://prove2.me/submissions/7606852a-8d79-475c-9cfc-e5451ea004d2

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate





theorem p2m_local_state_row_18 : StateFacts 18 := by decide



end Certificate
end Couret

theorem solution : Couret.Certificate.StateFacts
  (@OfNat.ofNat.{0} Couret.Certificate.StateId (nat_lit 18)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 147) (instOfNatNat (nat_lit 147)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) (nat_lit 18))) := @_root_.Couret.Certificate.p2m_local_state_row_18

