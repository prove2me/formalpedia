-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Affine.four_translated_affine_form
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:45:02.264183+00:00
-- url     : https://prove2.me/submissions/19ef55a9-75bb-485a-9ba1-cb4ec19b3dfb

import Definitions.Def_Couret_AffineSupportForms_4a272694daca
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
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_cyclic_step_unit_normalisation
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_four_lift_step_order
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts





theorem affine_image_of_translation (n : ℕ) (S : Finset (ZMod n)) (v : ZMod n) (u : (ZMod n)ˣ) :
    (S.image (fun z => z+v)).image (fun z => (u : ZMod n)*z)=
      S.image (fun z => (u : ZMod n)*z+(u : ZMod n)*v) := by
  rw [image_image]
  apply Finset.image_congr
  intro z hz
  change (u : ZMod n)*(z+v)=(u : ZMod n)*z+(u : ZMod n)*v
  ring



theorem p2m_local_four_translated_affine_form (m : ℕ) (hm : 0 < m) (S T : Finset (ZMod (2*m)))
    (h : FourTranslated m S T) : FourAffineForm m S T := by
  obtain ⟨v,r,c,d,hr,hc,hd,hS,hT⟩ := h
  obtain ⟨q,hq,hN,u,hu⟩ := cyclic_step_unit_normalisation (2*m) (by omega) r 8 (four_lift_step_order m hm r hr)
  let w : ZMod (2*m) := ↑(u⁻¹)
  have hq' : w*r=(q : ZMod (2*m)) := by dsimp [w]; rw [hu,← mul_assoc]; simp
  have hs : ∀ k : ℕ, w*(k • r)=k • (q : ZMod (2*m)) := by
    intro k
    rw [nsmul_eq_mul,nsmul_eq_mul]
    calc w*((k : ZMod (2*m))*r)=(k : ZMod (2*m))*(w*r) := by ring
         _=(k : ZMod (2*m))*(q : ZMod (2*m)) := by rw [hq']
  have hc' : w*c=2 • (q : ZMod (2*m)) ∨ w*c=6 • (q : ZMod (2*m)) := by
    rcases hc with hc|hc
    · left; rw [hc,hs]
    · right; rw [hc,hs]
  have hd' : w*d=3 • (q : ZMod (2*m)) ∨ w*d=7 • (q : ZMod (2*m)) := by
    rcases hd with hd|hd
    · left; rw [hd,hs]
    · right; rw [hd,hs]
  refine ⟨q,hq,hN,u⁻¹,w*v,w*c,w*d,hc',hd',?_,?_⟩
  · calc
      S.image (fun z => w*z+w*v)=(S.image (fun z => z+v)).image (fun z => w*z) :=
        (affine_image_of_translation (2*m) S v (u⁻¹)).symm
      _={w*c,w*d,0,4 • (q : ZMod (2*m))} := by
        rw [hS]
        simp only [image_insert,image_singleton,mul_zero,hs]
  · calc
      T.image (fun z => w*z+w*v)=(T.image (fun z => z+v)).image (fun z => w*z) :=
        (affine_image_of_translation (2*m) T v (u⁻¹)).symm
      _={w*c,w*d,(q : ZMod (2*m)),5 • (q : ZMod (2*m))} := by
        rw [hT]
        simp only [image_insert,image_singleton,hq',hs]

end Couret.InterIA.Catalogue.Affine

theorem solution : ∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
    ∀
      (S T :
        Finset.{0}
          (ZMod
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))),
      Couret.InterIA.Catalogue.Lifts.FourTranslated m S T → Couret.InterIA.Catalogue.Affine.FourAffineForm m S T := @_root_.Couret.InterIA.Catalogue.Affine.p2m_local_four_translated_affine_form

