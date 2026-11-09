-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.system_I_gcd_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:52:34.085988+00:00
-- url     : https://prove2.me/submissions/541779aa-e9ce-4a4d-b7dc-f6b2eee0ae7e

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_modulus_positive
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_I_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_system_scale_iff
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.AffineCriterion
open Couret.InterIA.NormalForm

theorem system_gcd_reduction (q X e k : ℕ) (hq : 0 < q) :
    System q X e k ↔ System (q / q.gcd X) (X / q.gcd X) e k := by
  let d := q.gcd X
  let a := X/d
  let b := q/d
  have hd : 0 < d := Nat.pos_of_ne_zero (Nat.gcd_ne_zero_left (by omega))
  have hdb : d*b=q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q X)
  have hda : d*a=X := Nat.mul_div_cancel' (Nat.gcd_dvd_right q X)
  have hb : 0 < b := Nat.pos_of_mul_pos_left (hdb.symm ▸ hq)
  simpa only [hdb,hda] using system_scale_iff d b a e k hd hb





theorem p2m_local_system_I_gcd_iff (q X : ℕ) (hq : 0 < q) :
    System q X 1 1 ↔ (q / q.gcd X)%4=0 := by
  rw [system_gcd_reduction q X 1 1 hq]
  exact system_I_iff _ _ (reduced_modulus_positive q X hq) (reduced_coprime q X hq)















end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (q X : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) q →
    Iff
      (Couret.InterIA.Catalogue.Quarter.Arithmetic.System q X
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) q (Nat.gcd q X))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_system_I_gcd_iff

