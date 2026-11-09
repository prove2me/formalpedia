-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.evaluation_combination_zero
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:19.970356+00:00
-- url     : https://prove2.me/submissions/ac1e20f8-48db-43cb-98b4-7b9364a8b2b6

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
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G]





theorem p2m_local_evaluation_combination_zero (x : Fin 6 → G) (rows : List Vec)
    (coeff : List ℤ) (hr : ∀ v ∈ rows, evaluation x v = 0) :
    evaluation x (combination rows coeff) = 0 := by
  induction rows generalizing coeff with
  | nil => simp [combination]
  | cons v vs ih =>
    cases coeff with
    | nil => simp [combination]
    | cons c cs =>
      have hv := hr v (by simp)
      have ht : ∀ w ∈ vs, evaluation x w = 0 := by
        intro w hw
        exact hr w (by simp [hw])
      change evaluation x (c • v + combination vs cs) = 0
      rw [map_add, map_zsmul, hv, ih cs ht]
      simpa only [add_zero] using (zsmul_zero (α := G) c)



end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G)
  (rows : List.{0} Couret.InterIA.SingletonNecessity.Vec) (coeff : List.{0} Int),
  (∀ (v : Couret.InterIA.SingletonNecessity.Vec),
      @Membership.mem.{0, 0} Couret.InterIA.SingletonNecessity.Vec (List.{0} Couret.InterIA.SingletonNecessity.Vec)
          (@List.instMembership.{0} Couret.InterIA.SingletonNecessity.Vec) rows v →
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
    @Eq.{p2m_u_0 + 1} G
      (@DFunLike.coe.{p2m_u_0 + 1, 1, p2m_u_0 + 1}
        (@AddMonoidHom.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
          (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
            (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (fun a => Int)
              fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
          (@AddZeroClass.toAddZero.{p2m_u_0} G
            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
        Couret.InterIA.SingletonNecessity.Vec (fun x => G)
        (@AddMonoidHom.instFunLike.{0, p2m_u_0} Couret.InterIA.SingletonNecessity.Vec G
          (@AddZeroClass.toAddZero.{0} Couret.InterIA.SingletonNecessity.Vec
            (@Pi.addZeroClass.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (fun a => Int)
              fun i => @AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid))
          (@AddZeroClass.toAddZero.{p2m_u_0} G
            (@AddMonoid.toAddZeroClass.{p2m_u_0} G
              (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))))))
        (@Couret.InterIA.SingletonNecessity.evaluation.{p2m_u_0} G inst x)
        (Couret.InterIA.SingletonNecessity.combination rows coeff))
      (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
        (@Zero.toOfNat0.{p2m_u_0} G
          (@NegZeroClass.toZero.{p2m_u_0} G
            (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
              (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                  (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_evaluation_combination_zero

