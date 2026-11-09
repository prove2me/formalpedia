-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.negative_system_sufficient
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:57.610021+00:00
-- url     : https://prove2.me/submissions/3e76b440-f49d-4983-a43b-3651afe86b46

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





/-- Systems III and IV have the same multiplier; its action on a depends on parity. -/
theorem p2m_local_negative_system_sufficient (b a k : ℕ) (hb : 0 < b)
    (hbo : b%2=1) (hk : k=0 ∨ k=2) (ha : (2*a)%4=(k*b)%4) :
    System b a 3 k := by
  have ho : (1+2*b)%2=1 := by omega
  let u := ZMod.unitOfCoprime (1+2*b) (one_add_mul_coprime b 2 ho)
  refine ⟨u,?_,?_⟩
  · apply (quarter_action_iff b (1+2*b) 3 hb).mpr
    omega
  · have hh : 2*a ≡ k*b [MOD 4] := ha
    have hbk : b*(k*b) ≡ k*b [MOD 4*b] := by
      have hb4 : (k*b)%4=k%4 := by rcases hk with rfl|rfl <;> omega
      have h := (show k*b ≡ k [MOD 4] from hb4).mul_left' b
      simpa only [mul_comm b k,mul_comm b 4] using h
    have he : (1+2*b)*a ≡ a+k*b [MOD 4*b] := by
      have hh0 : b*(2*a) ≡ b*(k*b) [MOD 4*b] := by
        simpa only [mul_comm b 4] using hh.mul_left' b
      have hh' := hh0.trans hbk
      convert (hh'.add_left a) using 1; ring
    simpa only [u,ZMod.coe_unitOfCoprime,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr he









end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (b a k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) b
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k b)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
          Couret.InterIA.Catalogue.Quarter.Arithmetic.System b a
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) k := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_negative_system_sufficient

