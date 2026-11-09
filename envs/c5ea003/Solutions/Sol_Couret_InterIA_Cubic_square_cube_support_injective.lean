-- Prove2me | solution 1 for Couret.InterIA.Cubic.square_cube_support_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:37.725419+00:00
-- url     : https://prove2.me/submissions/31d24e75-f392-4a87-ab8f-5a4d8d09c179

import Definitions.Def_Couret_CubicSupport_513df21f9351
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
import Theorems.Thm_Couret_InterIA_Cubic_cconv_indicator_left
import Theorems.Thm_Couret_InterIA_Cubic_square_cube_injective
import Definitions.Def_Couret_CubicFourier_396e42df2f8b
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.Cubic
open Finset Couret.InterIA.Parity





theorem cconv_comm {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (f g : G → ℂ) : cconv f g = cconv g f := by
  funext z
  unfold cconv
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [add_comm,mul_comm]



theorem complex_square_coefficient {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (z : G) :
    cconv (complexIndicator S) (complexIndicator S) z = (orderedSquare S z : ℂ) := by
  rw [cconv_indicator_left]
  simp only [orderedSquare,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hxy (y : G) : x+y=z ↔ y=z-x := by
    simp only [eq_sub_iff_add_eq,add_comm]
  simp [complexIndicator,hxy,Finset.sum_ite_eq']

theorem complex_cube_coefficient {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (z : G) :
    cconv (cconv (complexIndicator S) (complexIndicator S)) (complexIndicator S) z =
      (orderedCube S z : ℂ) := by
  rw [cconv_comm,cconv_indicator_left]
  simp only [complex_square_coefficient,orderedCube,Nat.cast_sum]

theorem p2m_local_square_cube_support_injective (n : ℕ) (hn : 0<n)
    (S T : Finset (ZMod n))
    (hs : ∀ z, orderedSquare S z=orderedSquare T z)
    (hc : ∀ z, orderedCube S z=orderedCube T z) : S=T := by
  letI : NeZero n := ⟨by omega⟩
  have hsq : cconv (complexIndicator S) (complexIndicator S) =
      cconv (complexIndicator T) (complexIndicator T) := by
    funext z
    simp only [complex_square_coefficient,hs z]
  have hcu : cconv (cconv (complexIndicator S) (complexIndicator S)) (complexIndicator S) =
      cconv (cconv (complexIndicator T) (complexIndicator T)) (complexIndicator T) := by
    funext z
    simp only [complex_cube_coefficient,hc z]
  have he := square_cube_injective (complexIndicator S) (complexIndicator T) hsq hcu
  ext x
  have h := congrFun he x
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp_all [complexIndicator]







end Couret.InterIA.Cubic

theorem solution : ∀ (n : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    ∀ (S T : Finset.{0} (ZMod n)),
      (∀ (z : ZMod n),
          @Eq.{1} Nat
            (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
              (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n)
              S z)
            (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
              (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n))) (ZMod.decidableEq n)
              T z)) →
        (∀ (z : ZMod n),
            @Eq.{1} Nat
              (@Couret.InterIA.Cubic.orderedCube.{0} (ZMod n)
                (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                (ZMod.decidableEq n) S z)
              (@Couret.InterIA.Cubic.orderedCube.{0} (ZMod n)
                (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                (ZMod.decidableEq n) T z)) →
          @Eq.{1} (Finset.{0} (ZMod n)) S T := @_root_.Couret.InterIA.Cubic.p2m_local_square_cube_support_injective

