-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_prepared_core_eq_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:18.597146+00:00
-- url     : https://prove2.me/submissions/127ab107-7679-46d7-9288-9ef850889b21

import Aesop
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_encoding_interpret
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_prime
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_bank_root_primitive
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_bank_sign_coordinates
import Theorems.Thm_Couret_STROBO2TORS_recoh_early_coefficient_backend_decoder_eq_backend
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb

set_option autoImplicit false

/-!
The concrete cyclic decoder with early square and reading checks.

All bank parameters, coefficient encodings, binary coordinates, and square
support data are constructed by the cyclic interface.  This module uses
those data in the early-rejection control flow: check the representative's
square and binary/ternary readings, recover its translation, then retain the
independent full final check.  The guarded decoder is equal to the complete
typed coefficient decoder for every input, including rejected input.

The equality relates executable Lean definitions on typed data.  It does
not identify the external Python parser, caches, or runtime with those
definitions, nor does the candidate bound assert bit complexity.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



/-- The canonical bank discharges every role contract needed for reordering
the checks.  Only the reduced observed-coefficient condition remains here;
the guarded decoder below checks it on the input. -/
theorem p2m_local_recoh_cyclic_prepared_core_eq_coefficient
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohCyclicBankPrime q i) (recohCyclicBankDepth q i) (terms i)) :
    recohCyclicPreparedCore q entries terms = recohCyclicCoefficientCore q entries terms := by
  apply recoh_early_coefficient_backend_decoder_eq_backend
    (recohTypedSquareSupport entries) (recohTypedSquareValue entries)
    (recohProductHalf q) (recohProductTwoCoordinates q)
    (recohCyclicBankPrime q) (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms
    (recohCyclicObservedBank q) (recohCyclicBankRoot q)
    (fun i => recohCoefficientValue (recohCyclicBankRoot q i) (terms i))
  · exact recoh_typed_square_covered entries
  · exact recoh_cyclic_bank_prime q
  · exact recoh_cyclic_bank_root_primitive q
  · exact hred
  · exact recoh_cyclic_bank_encoding_interpret q
  · intro i; rfl
  · intro u i
    exact recoh_cyclic_binary_bank_sign_coordinates q (recohCanonicalPrimaryData q 2) u i
  · intro u i
    apply recoh_cyclic_ternary_bank_trivial_on_two q (recohCanonicalPrimaryData q 3)
      ⟨i.val, i.property.1⟩ u.val
    simpa only [recoh_mem_torsion_subgroup, two_nsmul] using u.property













end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohCyclicBankIndex d q → Couret.STROBO2TORS.RecohSparseTerms),
  (∀ (i : @Couret.STROBO2TORS.RecohCyclicBankIndex d q),
      Couret.STROBO2TORS.RecohCoefficientsReduced (@Couret.STROBO2TORS.recohCyclicBankPrime d q i)
        (@Couret.STROBO2TORS.recohCyclicBankDepth d q inst i) (terms i)) →
    @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@Couret.STROBO2TORS.recohCyclicPreparedCore d q inst entries terms)
      (@Couret.STROBO2TORS.recohCyclicCoefficientCore d q inst entries terms) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_prepared_core_eq_coefficient

