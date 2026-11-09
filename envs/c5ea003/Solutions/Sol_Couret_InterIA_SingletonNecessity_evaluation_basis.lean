-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.evaluation_basis
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:04.292231+00:00
-- url     : https://prove2.me/submissions/4dc7bfcc-7b90-43f5-b22a-9fc3e0cfc1e8

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



theorem p2m_local_evaluation_basis (x : Fin 6 → G) (n : Fin 6) :
    evaluation x (basis n.val) = x n := by
  change (∑ k : Fin 6, (if k.val=n.val then (1:ℤ) else 0) • x k) = x n
  have h : ∀ k : Fin 6, k.val=n.val ↔ k=n := fun _ => Fin.val_inj
  simp only [h,ite_smul,one_zsmul,zero_zsmul]
  rw [Finset.sum_ite_eq']
  simp





end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G)
  (n : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))),
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
      (Couret.InterIA.SingletonNecessity.basis
        (@Fin.val (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n)))
    (x n) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_evaluation_basis

