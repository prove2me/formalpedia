-- Prove2me | solution 1 for Couret.Certificate.quotientMachine_correct
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:31.643996+00:00
-- url     : https://prove2.me/submissions/69ae2a8f-de51-4d6b-a75d-778440327526

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_Certificate_quotient_congruence_checked
import Theorems.Thm_Couret_Certificate_quotient_initial
import Theorems.Thm_Couret_Certificate_quotient_output_checked
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

















































theorem quotientRun_congruence (i : StateId) (w : Word Symbol) :
    classOf (tableRun i w) = quotientRun (classOf i) w := by
  induction w with
  | empty => rfl
  | snoc w g ih =>
    change classOf (tableNext (tableRun i w) g) = quotientNext (quotientRun (classOf i) w) g
    rw [quotient_congruence_checked, ih]

theorem future_output (i : StateId) (w : Word Symbol) :
    tableOutput (tableRun i w) = quotientOutput (quotientRun (classOf i) w) := by
  rw [quotient_output_checked, quotientRun_congruence]























theorem quotientMachine_run (c : ClassId) (w : Word Symbol) :
    machineRun quotientMachine c w = quotientRun c w := by
  induction w with
  | empty => rfl
  | snoc w g ih => change quotientNext (machineRun quotientMachine c w) g = _; rw [ih]; rfl

theorem p2m_local_quotientMachine_correct (w : Word Symbol) :
    quotientMachine.output (machineRun quotientMachine quotientMachine.initial w) =
      tableOutput (tableRun 0 w) := by
  change quotientOutput (machineRun quotientMachine 0 w) = _
  rw [quotientMachine_run]
  have he := future_output 0 w
  rw [quotient_initial] at he
  exact he.symm

end Certificate
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Couret.Certificate.Symbol),
  @Eq.{1} Nat
    (@Couret.Certificate.ObservationMachine.output Couret.Certificate.ClassId Couret.Certificate.quotientMachine
      (@Couret.Certificate.machineRun Couret.Certificate.ClassId Couret.Certificate.quotientMachine
        (@Couret.Certificate.ObservationMachine.initial Couret.Certificate.ClassId Couret.Certificate.quotientMachine)
        w))
    (Couret.Certificate.tableOutput
      (Couret.Certificate.tableRun
        (@OfNat.ofNat.{0} Couret.Certificate.StateId (nat_lit 0)
          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 147) (instOfNatNat (nat_lit 147)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))) (nat_lit 0)))
        w)) := @_root_.Couret.Certificate.p2m_local_quotientMachine_correct

