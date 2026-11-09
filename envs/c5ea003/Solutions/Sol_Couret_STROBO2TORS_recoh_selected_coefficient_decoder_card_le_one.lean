-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_selected_coefficient_decoder_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:16.95319+00:00
-- url     : https://prove2.me/submissions/6bd5fdf7-15e6-46c8-ac2a-73ec0c6a783f

import Aesop
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_selected_coefficient_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_observation_injective_on_square
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497

set_option autoImplicit false

/-!
The typed coefficient decoder with all binary coordinates and at most one
ternary coordinate selected from the labelled square. The square selector
runs before observed character coefficients are supplied. Its exact integer
backend retains the previously certified half-sum and sign-recovery code.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



























































/-- Arbitrary typed observations either fail or determine at most one
support. This includes well-shaped but unrealizable square data. -/
theorem p2m_local_recoh_selected_coefficient_decoder_card_le_one
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) :
    (recohSelectedCoefficientDecoder q entries terms).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro S hS T hT
  have hs := (recoh_mem_selected_coefficient_decoder_iff q entries terms S).mp hS
  have ht := (recoh_mem_selected_coefficient_decoder_iff q entries terms T).mp hT
  exact recoh_selected_observation_injective_on_square q entries S T hs.2.1 ht.2.1
    (congrArg Prod.fst hs.2.2) (congrArg Prod.fst ht.2.2) (hs.2.2.trans ht.2.2.symm)

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
      (@Couret.STROBO2TORS.recohSelectedCoefficientDecoder d q inst entries terms))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_selected_coefficient_decoder_card_le_one

