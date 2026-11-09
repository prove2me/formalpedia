-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_rational_noisy_decoder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:43.225199+00:00
-- url     : https://prove2.me/submissions/d376c862-4766-4043-b310-913a8979bf91

import Aesop
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_bank_separated_two
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8

set_option autoImplicit false

/-!
Quantitative reconstruction with the square-selected minimum-size bank.
Each binary character is replaced by a prescribed odd power; the selected
ternary character and the measurement index type are unchanged.

The multipliers are parameters of the bank and are fixed before readings are
received. The quantitative theorems require a certified amplitude bound on
the square fibre. A separate square-only selector supplies these parameters
and that bound.

The rational-decoder bridges use a supplied candidate set contained in the
fibre. They do not introduce an executable enumeration of the ambient group
or its powerset. Prediction error is included in the uniqueness budget.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

































/-- Including the true candidate and budgeting both measurement and
prediction error upgrades the executable rational output to a singleton. -/
theorem p2m_local_recoh_stable_rational_noisy_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (multipliers : RecohEvenCoordinate q → ℕ) (hodd : ∀ i, Odd (multipliers i))
    (S : Finset ((i : Fin d) → ZMod (q i)))
    (hSR : orderedSquare S = recohTypedSquareValue entries)
    (hamp : ∀ T ∈ squareFibre S, ∀ i, 1 ≤ ‖recohSupportProbe
      (recohStableBinaryBank q multipliers i) T‖)
    (candidates : Finset (Finset ((i : Fin d) → ZMod (q i))))
    (hsub : candidates ⊆ squareFibre S)
    (predicted : Finset ((i : Fin d) → ZMod (q i)) →
      RecohSelectedBankIndex q entries → RecohRationalComplex)
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (radius : ℚ) (ε η : ℝ) (hradius : 0 ≤ radius)
    (B : Finset ((i : Fin d) → ZMod (q i))) (hB : B ∈ candidates)
    (hpred : ∀ T ∈ candidates, ∀ i, ‖recohRationalComplexValue (predicted T i) -
      recohSupportProbe (recohStableObservedBank q entries multipliers i) T‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (recohStableObservedBank q entries multipliers i) B‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ)) (hunique : (radius : ℝ) + η < 1) :
    recohRationalNoisyDecoder candidates predicted observed radius = {B} := by
  have hsep := recoh_stable_bank_separated_two q entries multipliers hodd S hSR hamp
  apply recoh_rational_noisy_decoder_singleton
    (fun T i => recohSupportProbe (recohStableObservedBank q entries multipliers i) T)
    candidates predicted observed radius ε η 2 hradius B hB ?_ hpred hobs hcomplete (by linarith)
  intro T hT U hU hTU
  exact hsep T (hsub hT) U (hsub hU) hTU

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (multipliers : @Couret.STROBO2TORS.RecohEvenCoordinate d q → Nat),
  (∀ (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q), @Odd.{0} Nat Nat.instSemiring (multipliers i)) →
    ∀ (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
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
        (∀ (T : Finset.{0} ((i : Fin d) → ZMod (q i))),
            @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                  (Finset.{0} ((i : Fin d) → ZMod (q i)))
                  (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
                (@Couret.STROBO2TORS.squareFibre.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                    @ZMod.fintype (q a) (inst a))
                  S)
                T →
              ∀ (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q),
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@Norm.norm.{0} Complex Complex.instNorm
                    (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                      (@Couret.STROBO2TORS.recohStableBinaryBank d q inst multipliers i) T))) →
          ∀ (candidates : Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))),
            @HasSubset.Subset.{0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                (@Finset.instHasSubset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) candidates
                (@Couret.STROBO2TORS.squareFibre.{0} ((i : Fin d) → ZMod (q i))
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                    @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                  (fun a b =>
                    @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                      (Fin.fintype d) a b)
                  (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                    @ZMod.fintype (q a) (inst a))
                  S) →
              ∀
                (predicted :
                  Finset.{0} ((i : Fin d) → ZMod (q i)) →
                    @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries →
                      Couret.STROBO2TORS.RecohRationalComplex)
                (observed :
                  @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohRationalComplex)
                (radius : Rat) (ε η : Real),
                @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) radius →
                  ∀ (B : Finset.{0} ((i : Fin d) → ZMod (q i))),
                    @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                        (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                        (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                          (Finset.{0} ((i : Fin d) → ZMod (q i)))
                          (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
                        candidates B →
                      (∀ (T : Finset.{0} ((i : Fin d) → ZMod (q i))),
                          @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                              (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                              (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                                (Finset.{0} ((i : Fin d) → ZMod (q i)))
                                (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
                              candidates T →
                            ∀ (i : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries),
                              @LE.le.{0} Real Real.instLE
                                (@Norm.norm.{0} Complex Complex.instNorm
                                  (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                                    (Couret.STROBO2TORS.recohRationalComplexValue (predicted T i))
                                    (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                                      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                                        @Ring.toAddCommGroup.{0} (ZMod (q i))
                                          (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                                      (@Couret.STROBO2TORS.recohStableObservedBank d q inst entries multipliers i) T)))
                                η) →
                        (∀ (i : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries),
                            @LE.le.{0} Real Real.instLE
                              (@Norm.norm.{0} Complex Complex.instNorm
                                (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                                  (Couret.STROBO2TORS.recohRationalComplexValue (observed i))
                                  (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
                                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                                      @Ring.toAddCommGroup.{0} (ZMod (q i))
                                        (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
                                    (@Couret.STROBO2TORS.recohStableObservedBank d q inst entries multipliers i) B)))
                              ε) →
                          @LE.le.{0} Real Real.instLE
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ε η)
                              (@Rat.cast.{0} Real Real.instRatCast radius) →
                            @LT.lt.{0} Real Real.instLT
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@Rat.cast.{0} Real Real.instRatCast radius) η)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                              @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                                (@Couret.STROBO2TORS.recohRationalNoisyDecoder.{0, 0}
                                  (Finset.{0} ((i : Fin d) → ZMod (q i)))
                                  (@Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries)
                                  (fun a b =>
                                    @Finset.decidableEq.{0} ((i : Fin d) → ZMod (q i))
                                      (fun a b =>
                                        @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a))
                                          (fun a => ZMod.decidableEq (q a)) (Fin.fintype d) a b)
                                      a b)
                                  (@instFintypeSum.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                                    (@Couret.STROBO2TORS.RecohSelectedTernaryIndex d q inst entries)
                                    (@Subtype.fintype.{0} (Fin d)
                                      (fun i =>
                                        @Dvd.dvd.{0} Nat Nat.instDvd
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
                                      (fun a =>
                                        Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (q a))
                                      (Fin.fintype d))
                                    (@Couret.STROBO2TORS.recohSelectedTernaryFintype d q inst entries))
                                  candidates predicted observed radius)
                                (@Singleton.singleton.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
                                  (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
                                  (@Finset.instSingleton.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) B) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_rational_noisy_decoder_singleton

