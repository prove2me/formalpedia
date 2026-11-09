-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Quarter.Arithmetic.system_scale_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:41:14.164148+00:00
-- url     : https://prove2.me/submissions/160be37b-3f53-4e72-88e0-19d4561389c2

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
import Definitions.Def_Couret_QuarterAffineCriterion_d1003281e8a6
import Mathlib.Data.ZMod.Units

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Arithmetic





theorem scaled_action_eq (d b a c t : ℕ) (hd : d ≠ 0) :
    (t : ZMod (4*(d*b)))*(d*a : ℕ)=(d*c : ℕ) ↔
      (t : ZMod (4*b))*(a : ZMod (4*b))=c := by
  have he : 4*(d*b)=d*(4*b) := by ring
  rw [he]
  have h := scaled_cast_eq d (4*b) (t*a) c hd
  simp only [Nat.cast_mul] at h ⊢
  rw [show (d : ZMod (d*(4*b)))*((t : ZMod (d*(4*b)))*a)=t*(d*a) by ring] at h
  exact h

theorem p2m_local_system_scale_iff (d b a e k : ℕ) (hd : 0 < d) (hb : 0 < b) :
    System (d*b) (d*a) e k ↔ System b a e k := by
  have hn : NeZero (4*(d*b)) := ⟨Nat.ne_of_gt (by positivity)⟩
  have hm : NeZero (4*b) := ⟨by omega⟩
  have hdiv : 4*b ∣ 4*(d*b) := ⟨d,by ring⟩
  have transfer : ∀ (u : (ZMod (4*(d*b)))ˣ) (v : (ZMod (4*b))ˣ)
      (huv : ZMod.unitsMap hdiv u=v),
      ((u : ZMod (4*(d*b)))*(d*b : ℕ)=e*(d*b) ∧
       (u : ZMod (4*(d*b)))*(d*a : ℕ)=d*a+k*(d*b)) ↔
      ((v : ZMod (4*b)))*(b : ZMod (4*b))=e*b ∧
       (v : ZMod (4*b))*(a : ZMod (4*b))=a+k*b := by
    intro u v huv
    have hv : (u.val.val : ZMod (4*b))=(v : ZMod (4*b)) := by
      have hh := congrArg Units.val huv
      change (ZMod.castHom hdiv (ZMod (4*b))) (u : ZMod (4*(d*b)))=(v : ZMod (4*b)) at hh
      rw [← ZMod.natCast_zmod_val (u : ZMod (4*(d*b))),map_natCast] at hh
      exact hh
    have h1 := scaled_action_eq d b b (e*b) u.val.val (by omega)
    have h2 := scaled_action_eq d b a (a+k*b) u.val.val (by omega)
    rw [show d*(e*b)=e*(d*b) by ring] at h1
    rw [show d*(a+k*b)=d*a+k*(d*b) by ring] at h2
    simpa only [Nat.cast_mul,Nat.cast_add,ZMod.natCast_zmod_val,hv] using and_congr h1 h2
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨ZMod.unitsMap hdiv u,(transfer u _ rfl).mp (by simpa only [Nat.cast_mul] using hu)⟩
  · rintro ⟨v,hv⟩
    obtain ⟨u,hu⟩ := ZMod.unitsMap_surjective hdiv v
    exact ⟨u,by simpa only [Nat.cast_mul] using (transfer u v hu).mpr hv⟩

end Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem solution : ∀ (d b a e k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b →
      Iff
        (Couret.InterIA.Catalogue.Quarter.Arithmetic.System
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d b)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) d a) e k)
        (Couret.InterIA.Catalogue.Quarter.Arithmetic.System b a e k) := @_root_.Couret.InterIA.Catalogue.Quarter.Arithmetic.p2m_local_system_scale_iff

