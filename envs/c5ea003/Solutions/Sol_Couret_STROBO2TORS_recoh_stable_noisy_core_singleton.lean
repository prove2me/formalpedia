-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_noisy_core_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:44:25.172483+00:00
-- url     : https://prove2.me/submissions/5cf49adf-8acd-4749-98a8-bf5fe0c1e601

import Aesop
import Definitions.Def_Couret_RecohStableReconstruction_da64f089b51e
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_square_representatives_complete
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_sign_decoder_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_bank_separated_two
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_amplitude
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_bank_sign_coordinates
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_multiplier_odd
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_predicted_reading_error
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636

set_option autoImplicit false

/-!
End-to-end stable reconstruction on explicit cyclic products.  The square
determines the bank, rational series determine the prediction centres, and
the decoder generates at most one candidate per square representative.
Precision is supplied by two natural numbers and checked by rational guards.
No complex comparison occurs in the executable definitions.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



/-- The fully specified square-only bank has uniform separation two. -/
theorem recoh_computed_stable_bank_separated
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i)))
    (hR : orderedSquare S = recohTypedSquareValue entries) :
    RecohProbeSeparated (recohComputedStableBank q entries) (squareFibre S) 2 := by
  apply recoh_stable_bank_separated_two q entries (recohStableBinaryMultiplier q entries)
    (recoh_stable_binary_multiplier_odd q entries) S hR
  intro T hT i
  have hTdata := (mem_squareFibre S T).mp hT
  apply recoh_stable_binary_amplitude q entries T hTdata.1
  funext z
  exact (hTdata.2 z).symm.trans (congrFun hR z)





















theorem recoh_stable_precision_budgets (epsilon : ℚ) (machinTerms taylorTerms : ℕ)
    (h : RecohStablePrecisionValid epsilon machinTerms taylorTerms) :
    0 ≤ recohStableAcceptanceRadius epsilon ∧
      0 ≤ (recohStablePredictionTolerance epsilon : ℝ) ∧
      (epsilon : ℝ) + (recohStablePredictionTolerance epsilon : ℝ) =
        (recohStableAcceptanceRadius epsilon : ℝ) ∧
      2 * ((recohStableAcceptanceRadius epsilon : ℝ) +
        (recohStablePredictionTolerance epsilon : ℝ)) < 2 := by
  have he0 : (0 : ℝ) ≤ epsilon := by exact_mod_cast h.1
  have he1 : (epsilon : ℝ) < 1 := by exact_mod_cast h.2.1
  dsimp [recohStableAcceptanceRadius, recohStablePredictionTolerance]
  push_cast
  refine ⟨by dsimp [RecohStablePrecisionValid] at h; linarith [h.1, h.2.1], ?_, rfl, ?_⟩ <;> linarith









theorem recoh_stable_representatives_subset
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i)))
    (hR : orderedSquare S = recohTypedSquareValue entries) :
    recohCyclicSquareRepresentatives q entries ⊆ squareFibre S := by
  intro B hB
  have hb := recoh_cyclic_square_representatives_sound q entries B hB
  apply (mem_squareFibre S B).mpr
  refine ⟨hb.1, ?_⟩
  intro z
  exact (congrFun hR z).trans (congrFun hb.2 z).symm

/-- The concrete decoder recovers the unknown support from its exact square
and rational observations within any certified absolute error below one. -/
theorem p2m_local_recoh_stable_noisy_core_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ)
    (hprecision : RecohStablePrecisionValid epsilon machinTerms taylorTerms)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (recohComputedStableBank q entries i) S‖ ≤ (epsilon : ℝ)) :
    recohStableNoisyCore q entries observed epsilon machinTerms taylorTerms = {S} := by
  have hb := recoh_stable_precision_budgets epsilon machinTerms taylorTerms hprecision
  apply recoh_noisy_sign_decoder_singleton
    (recohComputedStableBank q entries) S (recohCyclicSquareRepresentatives q entries)
    (recoh_stable_representatives_subset q entries S hR)
    (recoh_cyclic_square_representatives_complete q entries S hS hR)
    (recohProductTwoCoordinates q) Sum.inl
    (fun u j => recoh_stable_binary_bank_sign_coordinates q
      (recohStableBinaryMultiplier q entries) (recoh_stable_binary_multiplier_odd q entries) u j)
    (recohStablePredictedReading q entries machinTerms taylorTerms) observed
    (recohStableAcceptanceRadius epsilon) (epsilon : ℝ)
    (recohStablePredictionTolerance epsilon : ℝ) hb.1 hb.2.1
    (recoh_computed_stable_bank_separated q entries S hR)
  · intro B hB j
    have hBdata := recoh_cyclic_square_representatives_sound q entries B hB
    exact recoh_stable_binary_amplitude q entries B hBdata.1 hBdata.2 j
  · intro T hT i
    exact recoh_stable_predicted_reading_error q entries epsilon machinTerms taylorTerms
      hprecision T ((mem_squareFibre S T).mp hT).1 i
  · exact hobs
  · exact le_of_eq hb.2.2.1
  · exact hb.2.2.2











end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} (((i : Fin d) → ZMod (q i)) → Nat)
        (@Couret.STROBO2TORS.orderedSquare.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          S)
        (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          entries) →
      ∀
        (observed :
          @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohRationalComplex)
        (epsilon : Rat) (machinTerms taylorTerms : Nat),
        Couret.STROBO2TORS.RecohStablePrecisionValid epsilon machinTerms taylorTerms →
          (∀ (i : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries),
              @LE.le.{0} Real Real.instLE
                (@Norm.norm.{0} Complex Complex.instNorm
                  (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                    (Couret.STROBO2TORS.recohRationalComplexValue (observed i))
                    (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                      (@Couret.STROBO2TORS.recohComputedStableBank d q inst entries i) S)))
                (@Rat.cast.{0} Real Real.instRatCast epsilon)) →
            @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
              (@Couret.STROBO2TORS.recohStableNoisyCore d q inst entries observed epsilon machinTerms taylorTerms)
              (@Singleton.singleton.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                (@Finset.instSingleton.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_noisy_core_singleton

