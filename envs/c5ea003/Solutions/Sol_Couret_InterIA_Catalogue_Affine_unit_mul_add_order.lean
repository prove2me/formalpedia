-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Affine.unit_mul_add_order
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:32.019499+00:00
-- url     : https://prove2.me/submissions/51cba0ab-de8b-43a9-a175-6008a0fc81f8

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts

theorem p2m_local_unit_mul_add_order (n : ℕ) (u : (ZMod n)ˣ) (x : ZMod n) :
    addOrderOf ((u : ZMod n)*x)=addOrderOf x := by
  apply addOrderOf_eq_addOrderOf_iff.mpr
  intro k
  have hc : ∀ z : ZMod n, (u : ZMod n)*z=0 ↔ z=0 := by
    intro z
    constructor
    · intro h
      have hh := congrArg (fun y : ZMod n => (↑(u⁻¹) : ZMod n)*y) h
      simpa [← mul_assoc] using hh
    · intro h; rw [h,mul_zero]
  rw [nsmul_eq_mul,nsmul_eq_mul]
  have he : (k : ZMod n)*((u : ZMod n)*x)=(u : ZMod n)*((k : ZMod n)*x) := by ring
  rw [he]
  exact hc _







end Couret.InterIA.Catalogue.Affine

theorem solution : ∀ (n : Nat)
  (u :
    @Units.{0} (ZMod n)
      (@Semiring.toMonoid.{0} (ZMod n)
        (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n)))))
  (x : ZMod n),
  @Eq.{1} Nat
    (@addOrderOf.{0} (ZMod n)
      (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
      (@HMul.hMul.{0, 0, 0} (ZMod n) (ZMod n) (ZMod n)
        (@instHMul.{0} (ZMod n)
          (@Distrib.toMul.{0} (ZMod n)
            (@instDistribOfSemiring.{0} (ZMod n)
              (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))))
        (@Units.val.{0} (ZMod n)
          (@Semiring.toMonoid.{0} (ZMod n)
            (@CommSemiring.toSemiring.{0} (ZMod n) (@CommRing.toCommSemiring.{0} (ZMod n) (ZMod.commRing n))))
          u)
        x))
    (@addOrderOf.{0} (ZMod n)
      (@AddMonoidWithOne.toAddMonoid.{0} (ZMod n)
        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod n)
          (@Ring.toAddGroupWithOne.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))))
      x) := @_root_.Couret.InterIA.Catalogue.Affine.p2m_local_unit_mul_add_order

