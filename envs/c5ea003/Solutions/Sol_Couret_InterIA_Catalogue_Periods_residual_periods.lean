-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Periods.residual_periods
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:32:43.540378+00:00
-- url     : https://prove2.me/submissions/6d515d0e-fddc-448f-bfd8-198cadcbd765

import Definitions.Def_Couret_QuotientPeriods_cf8d74422994
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_residual_four_atoms
import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Periods
open Finset Couret.InterIA.Catalogue Couret.InterIA.Parity Couret.InterIA.Projection
variable {G : Type*} [AddCommGroup G] [DecidableEq G]













/-- Multiplicities are retained: the four exponents need not be distinct. -/
theorem p2m_local_residual_periods (m : ℕ) (C : Finset (ZMod (2*m))) (hC : C.card=2)
    (a b : ZMod (2*m)) (δ : ZMod m) (hδ : δ ≠ 0)
    (he : residual m C a b=A δ*residual m C a b) :
    addOrderOf δ=2 ∨ addOrderOf δ=4 := by
  obtain ⟨c,d,hcd,hCe,hfour⟩ := residual_four_atoms m C hC a b
  rw [hfour] at he
  exact four_atoms_periods (projection m c) (projection m d) (projection m a) (projection m b) δ hδ he





end Couret.InterIA.Catalogue.Periods

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
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
      (δ : ZMod m),
      @Ne.{1} (ZMod m) δ
          (@OfNat.ofNat.{0} (ZMod m) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod m)
              (@MulZeroClass.toZero.{0} (ZMod m)
                (@instMulZeroClassOfSemiring.{0} (ZMod m)
                  (@CommSemiring.toSemiring.{0} (ZMod m)
                    (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m))))))) →
        @Eq.{1} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring) (Couret.InterIA.Catalogue.residual m C a b)
            (@HMul.hMul.{0, 0, 0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
              (@instHMul.{0} (@AddMonoidAlgebra.{0, 0} Int (ZMod m) Int.instSemiring)
                (@AddMonoidAlgebra.instMul.{0, 0} Int (ZMod m) Int.instSemiring
                  (@Distrib.toAdd.{0} (ZMod m)
                    (@instDistribOfSemiring.{0} (ZMod m)
                      (@CommSemiring.toSemiring.{0} (ZMod m)
                        (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
              (@Couret.InterIA.Catalogue.A m δ) (Couret.InterIA.Catalogue.residual m C a b)) →
          Or
            (@Eq.{1} Nat
              (@addOrderOf.{0} (ZMod m)
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                    (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))
                δ)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Eq.{1} Nat
              (@addOrderOf.{0} (ZMod m)
                (@AddMonoidWithOne.toAddMonoid.{0} (ZMod m)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                    (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))
                δ)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := @_root_.Couret.InterIA.Catalogue.Periods.p2m_local_residual_periods

