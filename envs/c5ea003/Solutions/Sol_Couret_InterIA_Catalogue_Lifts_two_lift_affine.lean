-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Lifts.two_lift_affine
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:43:19.727893+00:00
-- url     : https://prove2.me/submissions/ba89c408-b3c6-43b4-bc77-21af610c04d6

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_odd_quarter_half_mul
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.NormalForm

/-- Multiplication by the half-period has only two possible values. -/
theorem half_mul_cases (m : ℕ) (hm : 0 < m) (x : ZMod (2*m)) :
    (m : ZMod (2*m))*x=0 ∨ (m : ZMod (2*m))*x=m := by
  apply Couret.InterIA.L4.doubling_kernel m hm
  calc (m : ZMod (2*m))*x+m*x=(m+m)*x := by ring
       _=0 := by rw [Couret.InterIA.L4.half_add_half,zero_mul]



/-- Explicit affine witness for every lifted period-two pair when m=2 mod 4. -/
theorem p2m_local_two_lift_affine (m : ℕ) (hm : 0 < m) (hmod : m%4=2)
    (S T : Finset (ZMod (2*m))) (h : TwoLift m S T) : AffineEquivalent S T := by
  obtain ⟨a,c,r,hr,hS,hT⟩ := h
  let u : ZMod (2*m) := 1+m
  have hh := Couret.InterIA.L4.half_add_half m
  have hmr := odd_quarter_half_mul m hm hmod r hr
  have hmm : (m : ZMod (2*m))*m=0 := by
    obtain ⟨k,hk⟩ : ∃ k : ℕ, m=2*k := ⟨m/2,by omega⟩
    have he : (m : ZMod (2*m))=2*(k : ZMod (2*m)) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ => (n : ZMod (2*m))) hk
    calc (m : ZMod (2*m))*m=(m+m)*k := by rw [he]; ring
         _=0 := by rw [hh,zero_mul]
  have huu : u*u=1 := by dsimp [u]; linear_combination hmm+hh
  let U : (ZMod (2*m))ˣ := ⟨u,u,huu,huu⟩
  have hur : u*r+r=0 := by dsimp [u]; linear_combination hr+hmr+hh
  have hu2 : u*(2 • r)=2 • r := by
    simp only [two_nsmul]
    calc u*(r+r)=u*m := by rw [hr]
         _=m := by dsimp [u]; linear_combination hmm
         _=r+r := hr.symm
  have hu3 : u*(3 • r)=u*r+2 • r := by
    rw [show (3 : ℕ)=1+2 from rfl,add_nsmul,one_nsmul,mul_add,hu2]
  refine ⟨U,c+r-u*c,?_⟩
  change S.image (fun z => u*z+(c+r-u*c))=T
  have hc : u*c+(c+r-u*c)=c+r := by ring
  have hcr : u*(c+r)+(c+r-u*c)=c := by linear_combination hur
  have ha : u*a+(c+r-u*c)=a+r+(m : ZMod (2*m))*(a-c) := by dsimp [u]; ring
  have ha2 : u*(a+2 • r)+(c+r-u*c)=a+r+(m : ZMod (2*m))*(a-c)+2 • r := by rw [mul_add,hu2]; ring
  rw [hS,hT]
  simp only [image_insert,image_singleton,hc,hcr,ha,ha2]
  rcases half_mul_cases m hm (a-c) with he|he
  · rw [he,add_zero]
    ext z
    simp only [mem_insert,mem_singleton]
    have he3 : a+r+2 • r=a+3 • r := by simp only [succ_nsmul,zero_nsmul,zero_add]; abel
    rw [he3]
    tauto
  · rw [he,← hr]
    have he3 : a+r+(r+r)=a+3 • r := by simp only [succ_nsmul,zero_nsmul,zero_add]; abel
    have he1 : a+r+(r+r)+2 • r=a+r := by
      simp only [two_nsmul]
      linear_combination 2*hr+hh
    rw [he1,he3]
    ext z
    simp only [mem_insert,mem_singleton]
    tauto

end Couret.InterIA.Catalogue.Lifts

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) m
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀
        (S T :
          Finset.{0}
            (ZMod
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
        Couret.InterIA.Catalogue.Lifts.TwoLift m S T →
          @Couret.InterIA.NormalForm.AffineEquivalent
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)
            S T := @_root_.Couret.InterIA.Catalogue.Lifts.p2m_local_two_lift_affine

