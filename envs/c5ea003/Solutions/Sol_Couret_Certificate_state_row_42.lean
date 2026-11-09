-- Prove2me | solution 1 for Couret.Certificate.state_row_42
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:23:12.060132+00:00
-- url     : https://prove2.me/submissions/c3920b9b-ec0d-4045-9c67-7c51b820385f

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate

theorem p2m_local_state_row_42 : StateFacts 42 := by decide







end Certificate
end Couret

theorem solution : Couret.Certificate.StateFacts
  (@OfNat.ofNat.{0} Couret.Certificate.StateId (nat_lit 42)
    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 147) (instOfNatNat (nat_lit 147)))
      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) (nat_lit 42))) := @_root_.Couret.Certificate.p2m_local_state_row_42

