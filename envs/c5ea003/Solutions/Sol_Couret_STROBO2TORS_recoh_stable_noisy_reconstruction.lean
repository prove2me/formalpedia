-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_noisy_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:58:18.909614+00:00
-- url     : https://prove2.me/submissions/5ae08f95-5976-4a5c-b94e-6487e816cb8a

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_noisy_core_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_precision_parameters_exist
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_format_check_iff
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

/-- Valid finite approximation parameters exist for every admissible noise
budget, including budgets arbitrarily close to one. -/
theorem recoh_stable_precision_exists (epsilon : ℚ)
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    ∃ machinTerms taylorTerms, RecohStablePrecisionValid epsilon machinTerms taylorTerms := by
  obtain ⟨m, n, _hm, hpi, hn, herr⟩ := recoh_stable_precision_parameters_exist epsilon he1
  exact ⟨m, n, he0, he1, hpi, hn, herr⟩

















/-- All format and approximation guards are part of the executable contract. -/
theorem recoh_stable_noisy_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (hformat : RecohTypedSquareFormat entries)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ)
    (hprecision : RecohStablePrecisionValid epsilon machinTerms taylorTerms)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (recohComputedStableBank q entries i) S‖ ≤ (epsilon : ℝ)) :
    recohStableNoisyDecoder q entries observed epsilon machinTerms taylorTerms = {S} := by
  rw [recohStableNoisyDecoder,
    (recoh_typed_square_format_check_iff entries).mpr hformat,
    (recoh_stable_precision_check_iff epsilon machinTerms taylorTerms).mpr hprecision]
  exact recoh_stable_noisy_core_singleton q entries S hS hR observed epsilon
    machinTerms taylorTerms hprecision hobs





/-- Full existence contract: every absolute noise budget below one admits
finite checked parameters for which the concrete typed decoder returns
exactly the true support, using the bank computed from the square. -/
theorem p2m_local_recoh_stable_noisy_reconstruction
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (hformat : RecohTypedSquareFormat entries)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (recohComputedStableBank q entries i) S‖ ≤ (epsilon : ℝ)) :
    ∃ machinTerms taylorTerms,
      RecohStablePrecisionValid epsilon machinTerms taylorTerms ∧
      recohStableNoisyDecoder q entries observed epsilon machinTerms taylorTerms = {S} := by
  obtain ⟨m, n, hprecision⟩ := recoh_stable_precision_exists epsilon he0 he1
  exact ⟨m, n, hprecision, recoh_stable_noisy_decoder_singleton q entries hformat S hS hR
    observed epsilon m n hprecision hobs⟩

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)),
  @Couret.STROBO2TORS.RecohTypedSquareFormat.{0} ((i : Fin d) → ZMod (q i)) entries →
    ∀ (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
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
            (epsilon : Rat),
            @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) epsilon →
              @LT.lt.{0} Rat Rat.instLT epsilon (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))) →
                (∀ (i : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries),
                    @LE.le.{0} Real Real.instLE
                      (@Norm.norm.{0} Complex Complex.instNorm
                        (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                          (Couret.STROBO2TORS.recohRationalComplexValue (observed i))
                          (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                              @Ring.toAddCommGroup.{0} (ZMod (q i))
                                (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                            (@Couret.STROBO2TORS.recohComputedStableBank d q inst entries i) S)))
                      (@Rat.cast.{0} Real Real.instRatCast epsilon)) →
                  @Exists.{1} Nat fun machinTerms =>
                    @Exists.{1} Nat fun taylorTerms =>
                      And (Couret.STROBO2TORS.RecohStablePrecisionValid epsilon machinTerms taylorTerms)
                        (@Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                          (@Couret.STROBO2TORS.recohStableNoisyDecoder d q inst entries observed epsilon machinTerms
                            taylorTerms)
                          (@Singleton.singleton.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                            (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                            (@Finset.instSingleton.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_noisy_reconstruction

