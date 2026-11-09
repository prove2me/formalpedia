-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_mem_selected_coefficient_decoder_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:18:43.396659+00:00
-- url     : https://prove2.me/submissions/731513fa-d7c5-4615-a253-5dcb16161df8

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_all_coefficient_formats_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_coefficient_core_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_format_check_iff
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













































theorem recoh_selected_input_check_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms) :
    recohSelectedInputCheck q entries terms = true ↔ RecohSelectedInputFormat q entries terms := by
  simp [recohSelectedInputCheck, RecohSelectedInputFormat,
    recoh_typed_square_format_check_iff, recoh_all_coefficient_formats_iff, and_assoc]



theorem recoh_selected_coefficient_decoder_eq_exact
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms)
    (hformat : RecohSelectedInputFormat q entries terms) :
    recohSelectedCoefficientDecoder q entries terms =
      recohExactDecoder (recohSelectedObservedBank q entries)
        (recohSelectedTypedObservation q entries terms) := by
  rw [recohSelectedCoefficientDecoder,
    if_pos ((recoh_selected_input_check_iff q entries terms).mpr hformat)]
  exact recoh_selected_coefficient_core_eq_exact q entries terms (fun i => (hformat.2.2.2 i).1)

theorem recoh_selected_coefficient_decoder_rejects
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms)
    (hformat : ¬ RecohSelectedInputFormat q entries terms) :
    recohSelectedCoefficientDecoder q entries terms = ∅ := by
  simp only [recohSelectedCoefficientDecoder]
  rw [if_neg (fun h => hformat ((recoh_selected_input_check_iff q entries terms).mp h))]

/-- Membership means exactly a valid typed input and the selected labelled
observation of a triple. -/
theorem p2m_local_recoh_mem_selected_coefficient_decoder_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    S ∈ recohSelectedCoefficientDecoder q entries terms ↔
      RecohSelectedInputFormat q entries terms ∧ S.card = 3 ∧
        recohObservation (recohSelectedObservedBank q entries) S =
          recohSelectedTypedObservation q entries terms := by
  by_cases hformat : RecohSelectedInputFormat q entries terms
  · rw [recoh_selected_coefficient_decoder_eq_exact q entries terms hformat,
      recoh_mem_exact_decoder_iff]
    simp only [hformat, true_and]
  · rw [recoh_selected_coefficient_decoder_rejects q entries terms hformat]
    simp [hformat]







end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms)
  (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  Iff
    (@Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i))) (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
        (Finset.{0} ((i : Fin d) → ZMod (q i))) (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
      (@Couret.STROBO2TORS.recohSelectedCoefficientDecoder d q inst entries terms) S)
    (And (@Couret.STROBO2TORS.RecohSelectedInputFormat d q inst entries terms)
      (And
        (@Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Eq.{1}
          (Prod.{0, 0} (((i : Fin d) → ZMod (q i)) → Nat)
            (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Complex))
          (@Couret.STROBO2TORS.recohObservation.{0, 0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
            (@Couret.STROBO2TORS.recohSelectedObservedBank d q inst entries) S)
          (@Couret.STROBO2TORS.recohSelectedTypedObservation d q inst entries terms)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_mem_selected_coefficient_decoder_iff

