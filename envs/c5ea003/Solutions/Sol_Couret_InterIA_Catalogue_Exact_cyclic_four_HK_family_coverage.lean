-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.cyclic_four_HK_family_coverage
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:52:51.702577+00:00
-- url     : https://prove2.me/submissions/a310e07e-f6e5-48e5-9ad5-4e398d23062b

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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_cyclic_four_historical_catalogue_iff
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_historical_catalogue_generates_family
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient



















/-- H_K coverage in its finite cyclic four-point scope, by FAMILY_C4M alone. -/
theorem p2m_local_cyclic_four_HK_family_coverage (n : ℕ) (hn : 4 ≤ n) (S T : Finset (ZMod n))
    (hS : S.card=4) (hT : T.card=4) (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    AffineEquivalent S T ∨ ClassicalFamilyCatalogue n S T := by
  by_cases ha : AffineEquivalent S T
  · exact Or.inl ha
  · right
    apply historical_catalogue_generates_family n S T
    exact (cyclic_four_historical_catalogue_iff n hn S T).mp ⟨hS,hT,hsq,ha⟩

end Couret.InterIA.Catalogue.Exact

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
            Or (@Couret.InterIA.NormalForm.AffineEquivalent n S T)
              (Couret.InterIA.Catalogue.Exact.ClassicalFamilyCatalogue n S T) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_cyclic_four_HK_family_coverage

