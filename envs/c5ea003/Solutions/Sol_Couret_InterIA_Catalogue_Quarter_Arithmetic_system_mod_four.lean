-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.system_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:41:08.863599+00:00
-- url     : https://prove2.me/submissions/56db5179-f206-4d4d-a850-8fb110d85a6a

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

/-- Every system implies the corresponding compatibility modulo four. -/
theorem p2m_local_system_mod_four (b a e k : ℕ) (hb : 0 < b) (h : System b a e k) :
    (e*a)%4=(a+k*b)%4 := by
  letI : NeZero (4*b) := ⟨by omega⟩
  obtain ⟨u,hq,hx⟩ := h
  have hq' : u.val.val%4=e%4 := (quarter_action_iff b u.val.val e hb).mp
    (by simpa only [ZMod.natCast_zmod_val] using hq)
  have hx' := congrArg (ZMod.castHom (show 4 ∣ 4*b from ⟨b,rfl⟩) (ZMod 4)) hx
  have hu : (u.val.val : ZMod 4)=(e : ZMod 4) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hq'
  have hx'' : (u.val.val : ZMod 4)*(a : ZMod 4)=a+k*b := by
    rw [← ZMod.natCast_zmod_val (u : ZMod (4*b))] at hx'
    simpa only [map_mul,map_add,map_natCast] using hx'
  rw [hu] at hx''
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by simpa only [Nat.cast_mul,Nat.cast_add] using hx'')

























end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (b a e k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
    Couret.InterIA.Catalogue.Quarter.Arithmetic.System b a e k →
      @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) e a)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) k b))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_system_mod_four

