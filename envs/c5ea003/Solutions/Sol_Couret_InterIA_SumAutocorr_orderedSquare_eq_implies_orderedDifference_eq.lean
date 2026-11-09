-- Prove2me | solution 1 for Couret.InterIA.SumAutocorr.orderedSquare_eq_implies_orderedDifference_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:51:27.898003+00:00
-- url     : https://prove2.me/submissions/edfa5046-ff45-4577-8913-bef660e96d94

import Definitions.Def_Couret_SumAutocorr_074e6f9ba1f0
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SumAutocorr_dft_pairCount
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
namespace Couret.InterIA.SumAutocorr
open Finset Couret.InterIA.Parity

variable {n : ℕ} [NeZero n]









theorem standard_character_conjugate (z : ZMod n) :
    ZMod.stdAddChar (-z)=(starRingEnd ℂ) (ZMod.stdAddChar z) := by
  change (↑(ZMod.toCircle (-z)) : ℂ)=(starRingEnd ℂ) (↑(ZMod.toCircle z) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj (ZMod.toCircle z)



theorem dft_orderedSquare (S : Finset (ZMod n)) (k : ZMod n) :
    ZMod.dft (fun z => (orderedSquare S z : ℂ)) k=(supportFT S k)^2 := by
  change ZMod.dft (fun z => (pairCount S S (fun a b => a+b) z : ℂ)) k=_
  rw [dft_pairCount]
  have h (a b : ZMod n) : -( (a+b)*k)=-(a*k)+ -(b*k) := by ring
  simp_rw [h,AddChar.map_add_eq_mul]
  simp only [supportFT,pow_two,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem dft_orderedDifference (S : Finset (ZMod n)) (k : ZMod n) :
    ZMod.dft (fun z => (orderedDifference S z : ℂ)) k=
      supportFT S k*(starRingEnd ℂ) (supportFT S k) := by
  change ZMod.dft (fun z => (pairCount S S (fun a b => a-b) z : ℂ)) k=_
  rw [dft_pairCount]
  have h (a b : ZMod n) : -((a-b)*k)=-(a*k)+b*k := by ring
  have hc (b : ZMod n) : ZMod.stdAddChar (b*k)=
      (starRingEnd ℂ) (ZMod.stdAddChar (-(b*k))) := by
    simpa only [neg_neg] using standard_character_conjugate (-(b*k))
  simp_rw [h,AddChar.map_add_eq_mul,hc]
  simp only [supportFT,map_sum,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem complex_square_implies_conjugate_product {z w : ℂ} (h : z^2=w^2) :
    z*(starRingEnd ℂ) z=w*(starRingEnd ℂ) w := by
  have hf : (z-w)*(z+w)=0 := by
    calc (z-w)*(z+w)=z^2-w^2 := by ring
         _=0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hf with he|he
  · rw [sub_eq_zero.mp he]
  · have hz : z= -w := eq_neg_of_add_eq_zero_left he
    rw [hz]
    simp

/-- General finite cyclic implication: no cardinality, parity or classification hypothesis. -/
theorem p2m_local_orderedSquare_eq_implies_orderedDifference_eq
    (S T : Finset (ZMod n)) (h : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∀ z, orderedDifference S z=orderedDifference T z := by
  have hs : (fun z => (orderedSquare S z : ℂ))=
      (fun z => (orderedSquare T z : ℂ)) := by
    funext z
    rw [h z]
  have hc : (fun z => (orderedDifference S z : ℂ))=
      (fun z => (orderedDifference T z : ℂ)) := by
    apply (ZMod.dft (N := n) (E := ℂ)).injective
    funext k
    rw [dft_orderedDifference,dft_orderedDifference]
    apply complex_square_implies_conjugate_product
    calc
      (supportFT S k)^2=ZMod.dft (fun z => (orderedSquare S z : ℂ)) k :=
        (dft_orderedSquare S k).symm
      _=ZMod.dft (fun z => (orderedSquare T z : ℂ)) k :=
        congrArg (fun f : ZMod n → ℂ => ZMod.dft f k) hs
      _=(supportFT T k)^2 := dft_orderedSquare T k
  intro z
  exact_mod_cast congrFun hc z



end Couret.InterIA.SumAutocorr

theorem solution : ∀ {n : Nat} [@NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) n] (S T : Finset.{0} (ZMod n)),
  (∀ (z : ZMod n),
      @Eq.{1} Nat
        (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n) S
          z)
        (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
          (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n) T
          z)) →
    ∀ (z : ZMod n),
      @Eq.{1} Nat (@Couret.InterIA.SumAutocorr.orderedDifference n S z)
        (@Couret.InterIA.SumAutocorr.orderedDifference n T z) := @_root_.Couret.InterIA.SumAutocorr.p2m_local_orderedSquare_eq_implies_orderedDifference_eq

