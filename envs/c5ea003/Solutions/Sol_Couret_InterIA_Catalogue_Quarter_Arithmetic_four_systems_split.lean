-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.four_systems_split
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:33:58.325176+00:00
-- url     : https://prove2.me/submissions/ef08e84e-0857-4888-8195-f3f1e9508ae2

import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_four_quarters_zero
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm















theorem p2m_local_four_systems_split (q X : ℕ) :
    (∃ u, FourSystems q (X : ZMod (4*q)) u) ↔
      System q X 1 1 ∨ System q X 1 3 ∨ System q X 3 0 ∨ System q X 3 2 := by
  have he : (3 : ZMod (4*q))*q= -q := by
    have hh := four_quarters_zero q
    simp only [nsmul_eq_mul] at hh
    linear_combination hh
  simp only [System,FourSystems,Nat.cast_one,Nat.cast_ofNat,Nat.cast_zero,
    one_mul,zero_mul,add_zero,nsmul_eq_mul,he]
  constructor
  · rintro ⟨u,⟨hQ,hX|hX⟩|⟨hQ,hX|hX⟩⟩
    · exact Or.inl ⟨u,hQ,hX⟩
    · exact Or.inr (Or.inl ⟨u,hQ,hX⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨u,hQ,hX⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨u,hQ,hX⟩))
  · rintro (⟨u,hQ,hX⟩|⟨u,hQ,hX⟩|⟨u,hQ,hX⟩|⟨u,hQ,hX⟩)
    · exact ⟨u,Or.inl ⟨hQ,Or.inl hX⟩⟩
    · exact ⟨u,Or.inl ⟨hQ,Or.inr hX⟩⟩
    · exact ⟨u,Or.inr ⟨hQ,Or.inl hX⟩⟩
    · exact ⟨u,Or.inr ⟨hQ,Or.inr hX⟩⟩







end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (q X : Nat),
  Iff
    (@Exists.{1}
      (@Units.{0}
        (ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
        (@Semiring.toMonoid.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
          (@CommSemiring.toSemiring.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
            (@CommRing.toCommSemiring.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (ZMod.commRing
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))))
      fun u =>
      Couret.InterIA.Catalogue.Quarter.AffineCriterion.FourSystems q
        (@Nat.cast.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
          (@AddMonoidWithOne.toNatCast.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
            (@AddGroupWithOne.toAddMonoidWithOne.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Ring.toAddGroupWithOne.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                (@CommRing.toRing.{0}
                  (ZMod
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
                  (ZMod.commRing
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))))
          X)
        u)
    (Or
      (Couret.InterIA.Catalogue.Quarter.Arithmetic.System q X
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (Or
        (Couret.InterIA.Catalogue.Quarter.Arithmetic.System q X
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (Or
          (Couret.InterIA.Catalogue.Quarter.Arithmetic.System q X
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (Couret.InterIA.Catalogue.Quarter.Arithmetic.System q X
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_four_systems_split

