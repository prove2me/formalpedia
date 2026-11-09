-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_predicted_reading_error
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:31:06.960201+00:00
-- url     : https://prove2.me/submissions/cfcfbb4c-447c-4070-8161-3021904076a6

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_phase_center_error
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





























/-- Every predicted slot, binary or selected ternary, carries its error bound. -/
theorem p2m_local_recoh_stable_predicted_reading_error
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ)
    (hprecision : RecohStablePrecisionValid epsilon machinTerms taylorTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (i : RecohSelectedBankIndex q entries) :
    ‖recohRationalComplexValue (recohStablePredictedReading q entries machinTerms taylorTerms S i) -
      recohSupportProbe (recohComputedStableBank q entries i) S‖ ≤
        (recohStablePredictionTolerance epsilon : ℝ) := by
  have hbound : 3 * (recohRationalPhaseError machinTerms taylorTerms : ℝ) ≤
      (recohStablePredictionTolerance epsilon : ℝ) := by exact_mod_cast hprecision.2.2.2.2
  cases i with
  | inl j =>
    exact (recoh_support_phase_center_error q S hS j.val
      (2 ^ ((recohCanonicalPrimaryData q 2).exponent j + 1))
      (recoh_primary_factor_dvd q 2 (recohCanonicalPrimaryData q 2) j)
      (recohStableBinaryMultiplier q entries j) machinTerms taylorTerms
      hprecision.2.2.1 hprecision.2.2.2.1).trans hbound
  | inr j =>
    have h := recoh_support_phase_center_error q S hS j.val.val
      (3 ^ ((recohCanonicalPrimaryData q 3).exponent j.val + 1))
      (recoh_primary_factor_dvd q 3 (recohCanonicalPrimaryData q 3) j.val)
      1 machinTerms taylorTerms hprecision.2.2.1 hprecision.2.2.2.1
    simpa [recohStablePredictedReading, recohComputedStableBank,
      recohStableObservedBank, recohCyclicPrimaryBank] using h.trans hbound



















end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (epsilon : Rat) (machinTerms taylorTerms : Nat),
  Couret.STROBO2TORS.RecohStablePrecisionValid epsilon machinTerms taylorTerms →
    ∀ (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
      @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        ∀ (i : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries),
          @LE.le.{0} Real Real.instLE
            (@Norm.norm.{0} Complex Complex.instNorm
              (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                (Couret.STROBO2TORS.recohRationalComplexValue
                  (@Couret.STROBO2TORS.recohStablePredictedReading d q inst entries machinTerms taylorTerms S i))
                (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (@Couret.STROBO2TORS.recohComputedStableBank d q inst entries i) S)))
            (@Rat.cast.{0} Real Real.instRatCast (Couret.STROBO2TORS.recohStablePredictionTolerance epsilon)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_predicted_reading_error

