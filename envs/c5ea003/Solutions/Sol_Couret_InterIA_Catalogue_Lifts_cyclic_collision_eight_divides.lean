-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Lifts.cyclic_collision_eight_divides
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:08:35.809062+00:00
-- url     : https://prove2.me/submissions/58dac4b3-4901-4b66-9510-cd809cead919

import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
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
import Theorems.Thm_Couret_InterIA_Catalogue_Lifts_even_collision_eight_divides
import Theorems.Thm_Couret_InterIA_NormalForm_cyclic_four_L4
import Definitions.Def_Couret_OrbitLiftTranslation_2f31fa3b99fa
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Lifts
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Orbits
open Couret.InterIA.Parity





/-- Universal necessity for four-element supports with identical ordered SUM squares. -/
theorem p2m_local_cyclic_collision_eight_divides (n : ℕ) (hn : 4 ≤ n)
    (S T : Finset (ZMod n)) (hS : S.card=4) (hT : T.card=4)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z)
    (hnaff : ¬ AffineEquivalent S T) : 8 ∣ n := by
  obtain ⟨heven,_⟩ := cyclic_four_L4 n hn S T hS hT hsq hnaff
  obtain ⟨m,hm⟩ := heven
  have hnm : n=2*m := by omega
  clear hm
  subst n
  exact even_collision_eight_divides m (by omega) S T hS hT hsq hnaff

end Couret.InterIA.Catalogue.Lifts

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
              @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) n := @_root_.Couret.InterIA.Catalogue.Lifts.p2m_local_cyclic_collision_eight_divides

