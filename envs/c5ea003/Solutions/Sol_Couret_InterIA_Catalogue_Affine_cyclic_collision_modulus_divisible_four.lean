-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Affine.cyclic_collision_modulus_divisible_four
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:44.937875+00:00
-- url     : https://prove2.me/submissions/5ad4b425-c857-4778-a151-a6aab89b7f45

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
import Theorems.Thm_Couret_InterIA_Catalogue_Affine_collision_affine_forms
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Definitions.Def_Couret_AffineSupportForms_4a272694daca

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Affine
open Finset Couret.InterIA.Catalogue.Lifts Couret.InterIA.Parity



theorem collision_even_modulus_divisible_four (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) : 4 ∣ 2*m := by
  obtain ⟨t,ht,ho⟩ := collision_affine_forms m hm S T hS hT hsq hnaff
  rcases ho with ⟨q,hq,hN,rest⟩|⟨q,hq,hN,rest⟩
  · exact ⟨q,hN⟩
  · refine ⟨2*q,?_⟩
    omega

theorem p2m_local_cyclic_collision_modulus_divisible_four (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ Couret.InterIA.NormalForm.AffineEquivalent S T) : 4 ∣ n := by
  obtain ⟨heven,rest⟩ := Couret.InterIA.NormalForm.cyclic_four_L4 n hn S T hS hT hsq hnaff
  obtain ⟨m,hm⟩ := heven
  have he : n=2*m := by omega
  clear hm
  subst n
  exact collision_even_modulus_divisible_four m (by omega) S T hS hT hsq hnaff

end Couret.InterIA.Catalogue.Affine

theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    ∀ (S T : Finset.{0} (ZMod n)),
      @Eq.{1} Nat (@Finset.card.{0} (ZMod n) S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @Eq.{1} Nat (@Finset.card.{0} (ZMod n) T) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          (∀ (z : ZMod n),
              @Eq.{1} Nat
                (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
                  (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                  (ZMod.decidableEq n) S z)
                (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
                  (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                  (ZMod.decidableEq n) T z)) →
            Not (@Couret.InterIA.NormalForm.AffineEquivalent n S T) →
              @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n := @_root_.Couret.InterIA.Catalogue.Affine.p2m_local_cyclic_collision_modulus_divisible_four

