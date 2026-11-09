-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.positive_system_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:41:08.500447+00:00
-- url     : https://prove2.me/submissions/afae020c-9d06-4cda-b80a-8d8c238e49e2

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
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_scaled_cast_eq
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic

/-- Multiplication on a quarter reduces exactly to a congruence modulo four. -/
theorem quarter_action_iff (b t e : ℕ) (hb : 0 < b) :
    (t : ZMod (4*b))*(b : ZMod (4*b))=e*b ↔ t%4=e%4 := by
  have he := scaled_cast_eq b 4 t e (by omega)
  rw [show b*4=4*b by ring] at he
  simpa only [Nat.cast_mul,mul_comm (b : ZMod (4*b)),
    ZMod.natCast_eq_natCast_iff'] using he











/-- The only prime relevant to these explicit multipliers, beyond factors of b, is two. -/
theorem one_add_mul_coprime (b t : ℕ) (ho : (1+t*b)%2=1) :
    (1+t*b).Coprime (4*b) := by
  have h2 : (1+t*b).Coprime 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ho)
  have h4 : (1+t*b).Coprime 4 := by simpa using h2.pow_right 2
  have hb : (1+t*b).Coprime b := by simp [Nat.coprime_add_mul_right_left]
  exact h4.mul_right hb



/-- Explicit witness 1+k*b*a; no division by the parameter in the original group. -/
theorem p2m_local_positive_system_sufficient (b a k : ℕ) (hb : 0 < b)
    (hab : a.Coprime b) (h4 : b%4=0) : System b a 1 k := by
  have ha : a%2=1 := (coprime_not_both_even a b hab).resolve_right (by omega)
  have hm : (a*a)%4=1 := by
    have ha4 : a%4=1 ∨ a%4=3 := by omega
    rcases ha4 with hh|hh <;> simp [Nat.mul_mod,hh]
  have hb2 : b%2=0 := by omega
  have ho : (1+(k*a)*b)%2=1 := by simp [Nat.add_mod,Nat.mul_mod,hb2]
  let u := ZMod.unitOfCoprime (1+(k*a)*b) (one_add_mul_coprime b (k*a) ho)
  refine ⟨u,?_ ,?_⟩
  · change ((1+(k*a)*b : ℕ) : ZMod (4*b))*(b : ZMod (4*b))=(1 : ℕ)*b
    apply (quarter_action_iff b _ 1 hb).mpr
    simp [Nat.add_mod,Nat.mul_mod,h4]
  · change ((1+(k*a)*b : ℕ) : ZMod (4*b))*(a : ZMod (4*b))=a+k*b
    have hh : ((k*b)*(a*a))%(4*b)=(k*b)%(4*b) := by
      have hh : a*a ≡ 1 [MOD 4] := hm
      have he := hh.mul_left' (k*b)
      simpa only [mul_one] using he.of_dvd (show 4*b ∣ k*b*4 from ⟨k,by ring⟩)
    have he : (1+(k*a)*b)*a ≡ a+k*b [MOD 4*b] := by
      convert (Nat.ModEq.add_left a hh) using 1; ring
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr he











end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (b a k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
    Nat.Coprime a b →
      @Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        Couret.InterIA.Catalogue.Quarter.Arithmetic.System b a
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_positive_system_sufficient

