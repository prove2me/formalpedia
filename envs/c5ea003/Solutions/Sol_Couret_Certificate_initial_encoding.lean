-- Prove2me | solution 1 for Couret.Certificate.initial_encoding
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:37:03.003117+00:00
-- url     : https://prove2.me/submissions/eaebd612-72b8-4c8a-88bb-803fb27dc15b

import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Std
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
import Definitions.Def_Couret_CertificateData_653c7a96c17c
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
namespace Couret
namespace Certificate





theorem p2m_local_initial_encoding : entry 0 = none := by decide















end Certificate
end Couret

theorem solution : @Eq.{1} Couret.Certificate.EncodedState
  (Couret.Certificate.entry
    (@OfNat.ofNat.{0} Couret.Certificate.StateId (nat_lit 0)
      (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 147) (instOfNatNat (nat_lit 147)))
        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) (nat_lit 0))))
  (@Option.none.{0} (Prod.{0, 0} Couret.Certificate.Symbol Couret.Certificate.Mask)) := @_root_.Couret.Certificate.p2m_local_initial_encoding

