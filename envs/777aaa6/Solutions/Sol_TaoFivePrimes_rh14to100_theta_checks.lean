-- Prove2me | solution 1 for TaoFivePrimes.rh14to100_theta_checks
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T09:53:15.836787+00:00
-- url     : https://prove2.me/submissions/b7e8cfcf-a957-44a9-b342-f7e065ce8df8

/- Original finite validators and certificates: sometik179,
Prove2Me c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03).
Ordinary kernel proof adaptation; theta/Mellin attribution to Gabewhigham.
-/
import Definitions.Def_TaoFivePrimes_RH14To100ThetaInterface
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false
set_option linter.unusedSimpArgs false

namespace CertifiedJetRecords
open CertifiedThetaPoints
local instance cert_theta_decidableActive (i : Fin 16) (n : Fin 8) : Decidable (active i n) := by
  unfold active
  infer_instance

theorem cert_theta_row_checked_0 : ∀ n : Fin 8, active (0:Fin 16) n →
    checkRecord (0:Fin 16) n (recordAt (0:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_1 : ∀ n : Fin 8, active (1:Fin 16) n →
    checkRecord (1:Fin 16) n (recordAt (1:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_2 : ∀ n : Fin 8, active (2:Fin 16) n →
    checkRecord (2:Fin 16) n (recordAt (2:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_3 : ∀ n : Fin 8, active (3:Fin 16) n →
    checkRecord (3:Fin 16) n (recordAt (3:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_4 : ∀ n : Fin 8, active (4:Fin 16) n →
    checkRecord (4:Fin 16) n (recordAt (4:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_5 : ∀ n : Fin 8, active (5:Fin 16) n →
    checkRecord (5:Fin 16) n (recordAt (5:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_6 : ∀ n : Fin 8, active (6:Fin 16) n →
    checkRecord (6:Fin 16) n (recordAt (6:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_7 : ∀ n : Fin 8, active (7:Fin 16) n →
    checkRecord (7:Fin 16) n (recordAt (7:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_8 : ∀ n : Fin 8, active (8:Fin 16) n →
    checkRecord (8:Fin 16) n (recordAt (8:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_9 : ∀ n : Fin 8, active (9:Fin 16) n →
    checkRecord (9:Fin 16) n (recordAt (9:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_10 : ∀ n : Fin 8, active (10:Fin 16) n →
    checkRecord (10:Fin 16) n (recordAt (10:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_11 : ∀ n : Fin 8, active (11:Fin 16) n →
    checkRecord (11:Fin 16) n (recordAt (11:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_12 : ∀ n : Fin 8, active (12:Fin 16) n →
    checkRecord (12:Fin 16) n (recordAt (12:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_13 : ∀ n : Fin 8, active (13:Fin 16) n →
    checkRecord (13:Fin 16) n (recordAt (13:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_14 : ∀ n : Fin 8, active (14:Fin 16) n →
    checkRecord (14:Fin 16) n (recordAt (14:Fin 16) n)=true := by decide +kernel

theorem cert_theta_row_checked_15 : ∀ n : Fin 8, active (15:Fin 16) n →
    checkRecord (15:Fin 16) n (recordAt (15:Fin 16) n)=true := by decide +kernel

theorem cert_theta_records_checked : ∀ i : Fin 16, ∀ n : Fin 8,
    active i n → checkRecord i n (recordAt i n)=true := by
  intro i n h
  fin_cases i
  · exact cert_theta_row_checked_0 n h
  · exact cert_theta_row_checked_1 n h
  · exact cert_theta_row_checked_2 n h
  · exact cert_theta_row_checked_3 n h
  · exact cert_theta_row_checked_4 n h
  · exact cert_theta_row_checked_5 n h
  · exact cert_theta_row_checked_6 n h
  · exact cert_theta_row_checked_7 n h
  · exact cert_theta_row_checked_8 n h
  · exact cert_theta_row_checked_9 n h
  · exact cert_theta_row_checked_10 n h
  · exact cert_theta_row_checked_11 n h
  · exact cert_theta_row_checked_12 n h
  · exact cert_theta_row_checked_13 n h
  · exact cert_theta_row_checked_14 n h
  · exact cert_theta_row_checked_15 n h

end CertifiedJetRecords

theorem TaoFivePrimes.rh14to100_theta_checks (i : Fin 16) (n : Fin 8) (ha : CertifiedThetaPoints.active i n) :
    CertifiedJetRecords.checkRecord i n (CertifiedJetRecords.recordAt i n)=true := by
  exact CertifiedJetRecords.cert_theta_records_checked i n ha

theorem solution (i : Fin 16) (n : Fin 8) (ha : CertifiedThetaPoints.active i n) :
    CertifiedJetRecords.checkRecord i n (CertifiedJetRecords.recordAt i n)=true := TaoFivePrimes.rh14to100_theta_checks i n ha
