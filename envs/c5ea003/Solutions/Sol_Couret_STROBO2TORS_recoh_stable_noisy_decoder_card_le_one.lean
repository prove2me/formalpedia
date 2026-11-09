-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_noisy_decoder_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:00.207871+00:00
-- url     : https://prove2.me/submissions/00843b3a-d10d-4e15-aa93-42c555ab1560

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_sign_decoder_card_le_representatives
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_noisy_core_card_le_one
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





















theorem recoh_stable_precision_check_iff (epsilon : ℚ) (machinTerms taylorTerms : ℕ) :
    recohStablePrecisionCheck epsilon machinTerms taylorTerms = true ↔
      RecohStablePrecisionValid epsilon machinTerms taylorTerms := by
  simp [recohStablePrecisionCheck]





















/-- The guarded executable has at most one answer on every typed input,
including an unrealizable square or arbitrarily corrupted readings. -/
theorem p2m_local_recoh_stable_noisy_decoder_card_le_one
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ) :
    (recohStableNoisyDecoder q entries observed epsilon machinTerms taylorTerms).card ≤ 1 := by
  unfold recohStableNoisyDecoder
  split_ifs with hguard
  · have hchecks : recohTypedSquareFormatCheck entries = true ∧
        recohStablePrecisionCheck epsilon machinTerms taylorTerms = true := by
      simpa only [Bool.and_eq_true] using hguard
    have hprecision := (recoh_stable_precision_check_iff epsilon machinTerms taylorTerms).mp hchecks.2
    by_cases hex : (recohCyclicSquareRepresentatives q entries).Nonempty
    · obtain ⟨S, hS⟩ := hex
      exact recoh_stable_noisy_core_card_le_one q entries S
        (recoh_cyclic_square_representatives_sound q entries S hS).2
        observed epsilon machinTerms taylorTerms hprecision
    · have hempty : recohCyclicSquareRepresentatives q entries = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hex
      exact (recoh_noisy_sign_decoder_card_le_representatives
        (recohCyclicSquareRepresentatives q entries) (recohProductTwoCoordinates q) Sum.inl
        (recohStablePredictedReading q entries machinTerms taylorTerms)
        observed (recohStableAcceptanceRadius epsilon)).trans (by simp [hempty])
  · simp





end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (observed : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohRationalComplex)
  (epsilon : Rat) (machinTerms taylorTerms : Nat),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
      (@Couret.STROBO2TORS.recohStableNoisyDecoder d q inst entries observed epsilon machinTerms taylorTerms))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_noisy_decoder_card_le_one

