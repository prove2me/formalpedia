-- Prove2me | solution 1 for Couret.Certificate.state_row_98
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:24:45.111853+00:00
-- url     : https://prove2.me/submissions/17567a69-b8b8-4063-b860-1d09011a1389

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem p2m_local_state_row_98 : StateFacts 98 := by decide







end Certificate
end Couret

theorem solution : Couret.Certificate.StateFacts
  (@OfNat.ofNat.{0} Couret.Certificate.StateId (nat_lit 98)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 147) (instOfNatNat (nat_lit 147)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) (nat_lit 98))) := @_root_.Couret.Certificate.p2m_local_state_row_98

