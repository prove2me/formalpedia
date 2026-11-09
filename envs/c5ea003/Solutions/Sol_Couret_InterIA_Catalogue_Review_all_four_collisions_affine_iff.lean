-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Review.all_four_collisions_affine_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:49:29.099903+00:00
-- url     : https://prove2.me/submissions/4a76543a-cf17-4396-bd25-071a7ebb1923

import Aesop
import Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Basic
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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_dilated_reference_collision
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_cyclic_collision_eight_divides
import Definitions.Def_Couret_CyclicCatalogueEquivalence_bddddc095b9c

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Review
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Exact Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Primitive

/-- Expository corollary of the received necessity and constructive sufficiency. -/
theorem nonaffine_four_collision_exists_iff (n : ℕ) (hn : 4 ≤ n) :
    (∃ S T : Finset (ZMod n), FourCollision S T) ↔ 8 ∣ n := by
  constructor
  · rintro ⟨S,T,hS,hT,hsq,hna⟩
    exact Couret.InterIA.Catalogue.Lifts.cyclic_collision_eight_divides n hn S T hS hT hsq hna
  · rintro ⟨d,hd⟩
    have hdp : 0 < d := by omega
    refine ⟨(patternA 2 1).image (dilate n d), (patternB 2 1).image (dilate n d),?_⟩
    exact dilated_reference_collision n d 2 (by omega) hdp (by omega) (by decide)

theorem p2m_local_all_four_collisions_affine_iff (n : ℕ) (hn : 4 ≤ n) :
    (∀ S T : Finset (ZMod n), S.card=4 → T.card=4 →
      (∀ z, orderedSquare S z=orderedSquare T z) → AffineEquivalent S T) ↔ ¬ 8 ∣ n := by
  constructor
  · intro hall hdiv
    obtain ⟨S,T,hS,hT,hsq,hna⟩ := (nonaffine_four_collision_exists_iff n hn).mpr hdiv
    exact hna (hall S T hS hT hsq)
  · intro hdiv S T hS hT hsq
    by_contra hna
    exact hdiv ((nonaffine_four_collision_exists_iff n hn).mp ⟨S,T,hS,hT,hsq,hna⟩)

end Couret.InterIA.Catalogue.Review

theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    Iff
      (∀ (S T : Finset.{0} (ZMod n)),
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
              @Couret.InterIA.NormalForm.AffineEquivalent n S T)
      (Not (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) n)) := @_root_.Couret.InterIA.Catalogue.Review.p2m_local_all_four_collisions_affine_iff

