-- Prove2me | solution 1 for Couret.InterIA.QuotientBridge.residual_positive_mass
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:50:24.014757+00:00
-- url     : https://prove2.me/submissions/48167fb1-67d3-49b4-8af1-2a6d9b4c0602

import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_L4Assembly_154a326d9c14
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.QuotientBridge
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
open Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo Couret.InterIA.Projection











section Moment
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







end Moment

theorem residual_four_atoms (m : ℕ) (C : Finset (ZMod (2*m))) (hC : C.card=2)
    (a b : ZMod (2*m)) : ∃ c e : ZMod (2*m), c ≠ e ∧ C={c,e} ∧
    residual m C a b = atom (projection m c)+atom (projection m e)+
      atom (projection m a)+atom (projection m b) := by
  obtain ⟨c,e,hce,rfl⟩ := Finset.card_eq_two.mp hC
  exact ⟨c,e,hce,rfl,by simp only [residual,indicator_pair _ _ hce,map_add,push_atom]⟩







theorem mass_atom {G : Type*} [AddCommGroup G] (x : G) : mass (atom x) = 1 := by
  change Finsupp.liftAddHom (fun _ : G => AddMonoidHom.id ℤ) (Finsupp.single x (1 : ℤ)) = 1
  simp

/-- Positivity and total mass retain multiplicity in the quotient. -/
theorem p2m_local_residual_positive_mass (m : ℕ) (C : Finset (ZMod (2*m)))
    (hC : C.card=2) (a b : ZMod (2*m)) :
    (∀ z, 0 ≤ (residual m C a b).coeff z) ∧
      mass (residual m C a b) = 4 := by
  obtain ⟨c,e,_,_,hr⟩ := residual_four_atoms m C hC a b
  rw [hr]
  constructor
  · intro z
    change 0 ≤ (atom (projection m c)).coeff z + (atom (projection m e)).coeff z +
      (atom (projection m a)).coeff z + (atom (projection m b)).coeff z
    have hatom : ∀ x : ZMod m, (atom x).coeff z = if x=z then (1 : ℤ) else 0 := by
      intro x
      exact AddMonoidAlgebra.single_apply
    simp only [hatom]
    split_ifs <;> norm_num
  · simp only [map_add, mass_atom]
    norm_num





end Couret.InterIA.QuotientBridge

theorem solution : ∀ (m : Nat)
  (C :
    Finset.{0}
      (ZMod
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
  @Eq.{1} Nat
      (@Finset.card.{0}
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
        C)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    ∀
      (a b :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)),
      And
        (∀ (z : ZMod m),
          @LE.le.{0} Int Int.instLEInt (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
            (@DFunLike.coe.{1, 1, 1}
              (@Finsupp.{0, 0} (ZMod m) Int
                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
              (ZMod m) (fun x => Int)
              (@Finsupp.instFunLike.{0, 0} (ZMod m) Int
                (@MulZeroClass.toZero.{0} Int (@instMulZeroClassOfSemiring.{0} Int Int.instSemiring)))
              (@AddMonoidAlgebra.coeff.{0, 0} Int (ZMod m) Int.instSemiring
                (Couret.InterIA.QuotientBridge.residual m C a b))
              z))
        (@Eq.{1} Int
          (@DFunLike.coe.{1, 1, 1}
            (@AddMonoidHom.{0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring) Int
              (@AddZeroClass.toAddZero.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                (@AddMonoid.toAddZeroClass.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@AddMonoidWithOne.toAddMonoid.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@Ring.toAddGroupWithOne.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                        (@AddMonoidAlgebra.ring.{0, 0} Int (ZMod m) Int.instRing
                          (@SubNegMonoid.toAddMonoid.{0} (ZMod m)
                            (@AddGroup.toSubNegMonoid.{0} (ZMod m)
                              (@AddCommGroup.toAddGroup.{0} (ZMod m)
                                (@Ring.toAddCommGroup.{0} (ZMod m)
                                  (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m))))))))))))
              (@AddZeroClass.toAddZero.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)))
            (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring) (fun x => Int)
            (@AddMonoidHom.instFunLike.{0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring) Int
              (@AddZeroClass.toAddZero.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                (@AddMonoid.toAddZeroClass.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                  (@AddMonoidWithOne.toAddMonoid.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                      (@Ring.toAddGroupWithOne.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                        (@AddMonoidAlgebra.ring.{0, 0} Int (ZMod m) Int.instRing
                          (@SubNegMonoid.toAddMonoid.{0} (ZMod m)
                            (@AddGroup.toSubNegMonoid.{0} (ZMod m)
                              (@AddCommGroup.toAddGroup.{0} (ZMod m)
                                (@Ring.toAddCommGroup.{0} (ZMod m)
                                  (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m))))))))))))
              (@AddZeroClass.toAddZero.{0} Int (@AddMonoid.toAddZeroClass.{0} Int Int.instAddMonoid)))
            (@Couret.InterIA.QuotientBridge.mass.{0} (ZMod m)
              (@Ring.toAddCommGroup.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m))))
            (Couret.InterIA.QuotientBridge.residual m C a b))
          (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))) := @_root_.Couret.InterIA.QuotientBridge.p2m_local_residual_positive_mass

