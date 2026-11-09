-- Prove2me | solution 1 for Couret.InterIA.Catalogue.Exact.cyclic_four_historical_catalogue_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:44:20.212387+00:00
-- url     : https://prove2.me/submissions/7e27bd5f-24bb-4046-8f5a-18f64371fb88

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
import Theorems.Thm_Couret_InterIA_Catalogue_Exact_cyclic_collision_catalogue_iff
import Definitions.Def_Couret_ReferenceCatalogueConverse_0cbe68a31344
import Definitions.Def_Couret_InteriaC4m_265d5cdb2807

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Exact
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Catalogue.Quarter Couret.InterIA.Catalogue.Quarter.Primitive
open Couret.InterIA.Catalogue.Quarter.Ambient

theorem historical_T_identification (b : ℕ) : patternA b 1=Couret.InterIA.C4m.T b := by
  have h2 : (1 : ZMod (4*b))+2 • (b : ZMod (4*b))=((2*b+1 : ℕ) : ZMod (4*b)) := by
    simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring
  ext z <;> simp only [patternA,Couret.InterIA.C4m.T,h2,mem_insert,mem_singleton] <;> tauto

theorem historical_U_identification (b : ℕ) : patternB b 1=Couret.InterIA.C4m.U b := by
  have h1 : (1 : ZMod (4*b))+(b : ZMod (4*b))=((b+1 : ℕ) : ZMod (4*b)) := by
    simp only [Nat.cast_add,Nat.cast_one]; ring
  have h3 : (1 : ZMod (4*b))+3 • (b : ZMod (4*b))=((3*b+1 : ℕ) : ZMod (4*b)) := by
    simp only [nsmul_eq_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring
  ext z <;> simp only [patternB,Couret.InterIA.C4m.U,h1,h3,mem_insert,mem_singleton] <;> tauto





theorem historical_ambient_reference_iff (n : ℕ) (S T : Finset (ZMod n)) :
    AmbientReferenceForm n S T ↔ HistoricalReferenceForm n S T := by
  simp only [AmbientReferenceForm,HistoricalReferenceForm,historical_T_identification,historical_U_identification]



/-- Complete equivalence, using the historical T/U definitions without changing their source. -/
theorem p2m_local_cyclic_four_historical_catalogue_iff (n : ℕ) (hn : 4 ≤ n) (S T : Finset (ZMod n)) :
    (S.card=4 ∧ T.card=4 ∧ (∀ z, orderedSquare S z=orderedSquare T z) ∧
      ¬ AffineEquivalent S T) ↔ HistoricalCatalogue n S T := by
  change FourCollision S T ↔ HistoricalCatalogue n S T
  rw [cyclic_collision_catalogue_iff n hn S T]
  simp only [HistoricalCatalogue,historical_ambient_reference_iff]







end Couret.InterIA.Catalogue.Exact

theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) n →
    ∀ (S T : Finset.{0} (ZMod n)),
      Iff
        (And (@Eq.{1} Nat (@Finset.card.{0} (ZMod n) S) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (And (@Eq.{1} Nat (@Finset.card.{0} (ZMod n) T) (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (And
              (∀ (z : ZMod n),
                @Eq.{1} Nat
                  (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
                    (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                    (ZMod.decidableEq n) S z)
                  (@Couret.InterIA.Parity.orderedSquare.{0} (ZMod n)
                    (@Ring.toAddCommGroup.{0} (ZMod n) (@CommRing.toRing.{0} (ZMod n) (ZMod.commRing n)))
                    (ZMod.decidableEq n) T z))
              (Not (@Couret.InterIA.NormalForm.AffineEquivalent n S T)))))
        (Couret.InterIA.Catalogue.Exact.HistoricalCatalogue n S T) := @_root_.Couret.InterIA.Catalogue.Exact.p2m_local_cyclic_four_historical_catalogue_iff

