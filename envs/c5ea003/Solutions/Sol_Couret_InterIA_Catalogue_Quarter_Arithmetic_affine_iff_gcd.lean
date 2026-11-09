-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.affine_iff_gcd
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:13.182811+00:00
-- url     : https://prove2.me/submissions/3ea97273-2284-4b90-a985-0487c64158f1

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_AffineCriterion_affine_iff_four_systems
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_four_systems_split
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_III_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_II_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_IV_gcd_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_I_gcd_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

















/-- Exact arithmetic elimination of the unit existential, including nonunit parameters. -/
theorem four_systems_gcd_iff (q X : ℕ) (hq : 0 < q) :
    (∃ u, FourSystems q (X : ZMod (4*q)) u) ↔ (q/q.gcd X)%4 ≠ 2 := by
  rw [four_systems_split,system_I_gcd_iff q X hq,system_II_gcd_iff q X hq,
    system_III_gcd_iff q X hq,system_IV_gcd_iff q X hq]
  have hh := coprime_not_both_even _ _ (reduced_coprime q X hq)
  omega

/-- Reuses the received affine equivalence theorem rather than its geometric proof. -/
theorem p2m_local_affine_iff_gcd (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) :
    AffineEquivalent (patternA q x) (patternB q x) ↔ (q/q.gcd x.val)%4 ≠ 2 := by
  letI : NeZero (4*q) := ⟨by omega⟩
  rw [affine_iff_four_systems q hq x hx]
  simpa only [ZMod.natCast_zmod_val] using four_systems_gcd_iff q x.val hq



end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (q : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
    ∀
      (x :
        ZMod
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)),
      Not
          (@Membership.mem.{0, 0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
            (Finset.{0}
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
            (@SetLike.instMembership.{0, 0}
              (Finset.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)))
              (ZMod
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))
              (@Finset.instSetLike.{0}
                (ZMod
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q))))
            (Couret.InterIA.Catalogue.Quarter.badParameters q) x) →
        Iff
          (@Couret.InterIA.NormalForm.AffineEquivalent
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
            (Couret.InterIA.Catalogue.Quarter.patternA q x) (Couret.InterIA.Catalogue.Quarter.patternB q x))
          (@Ne.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) q
                (Nat.gcd q
                  (@ZMod.val
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                    x)))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_affine_iff_gcd

