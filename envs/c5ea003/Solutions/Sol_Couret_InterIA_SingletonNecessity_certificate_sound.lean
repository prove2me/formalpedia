-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.certificate_sound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:59:57.194821+00:00
-- url     : https://prove2.me/submissions/ab6437cc-5805-4fb7-879c-d46d6f0a6556

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_combination_zero
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G]







theorem p2m_local_certificate_sound (mixed : Bool) (c : Certificate)
    (hc : valid mixed c = true) (x : Fin 6 → G)
    (hr : ∀ v ∈ relations mixed c.perm, evaluation x v = 0) :
    c.i < c.j ∧ c.j < 7 ∧ evaluation x (label c.i) = evaluation x (label c.j) := by
  have h : c.i < c.j ∧ c.j < 7 ∧
      c.coeff.length = (relations mixed c.perm).length ∧
      combination (relations mixed c.perm) c.coeff = label c.i - label c.j := by
    simpa only [valid, decide_eq_true_eq] using hc
  refine ⟨h.1, h.2.1, ?_⟩
  have hz := evaluation_combination_zero x (relations mixed c.perm) c.coeff hr
  rw [h.2.2.2, map_sub] at hz
  exact sub_eq_zero.mp hz

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] (mixed : Bool)
  (c : Couret.InterIA.SingletonNecessity.Certificate),
  @Eq.{1} Bool (Couret.InterIA.SingletonNecessity.valid mixed c) Bool.true →
    ∀ (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
      (∀ (v : Couret.InterIA.SingletonNecessity.Vec),
          @Membership.mem.{0, 0} Couret.InterIA.SingletonNecessity.Vec (List.{0} Couret.InterIA.SingletonNecessity.Vec)
              (@List.instMembership.{0} Couret.InterIA.SingletonNecessity.Vec)
              (Couret.InterIA.SingletonNecessity.relations mixed (Couret.InterIA.SingletonNecessity.Certificate.perm c))
              v →
            @Eq.{p2m_u_0 + 1} G
              (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
                (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                Couret.InterIA.SingletonNecessity.Vec (fun x => G)
                (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x) v)
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst)))))))) →
        And
          (@LT.lt.{0} Nat instLTNat (Couret.InterIA.SingletonNecessity.Certificate.i c)
            (Couret.InterIA.SingletonNecessity.Certificate.j c))
          (And
            (@LT.lt.{0} Nat instLTNat (Couret.InterIA.SingletonNecessity.Certificate.j c)
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (@Eq.{p2m_u_0 + 1} G
              (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
                (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                Couret.InterIA.SingletonNecessity.Vec (fun x => G)
                (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x)
                (Couret.InterIA.SingletonNecessity.label (Couret.InterIA.SingletonNecessity.Certificate.i c)))
              (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
                (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                Couret.InterIA.SingletonNecessity.Vec (fun x => G)
                (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
                  (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
                    (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (fun a => Int) fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
                  (@AddZeroClass.toAddZero.{p2m_u_0} G
                    (@AddMonoid.toAddZeroClass.{p2m_u_0} G
                      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
                (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x)
                (Couret.InterIA.SingletonNecessity.label (Couret.InterIA.SingletonNecessity.Certificate.j c))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_certificate_sound

