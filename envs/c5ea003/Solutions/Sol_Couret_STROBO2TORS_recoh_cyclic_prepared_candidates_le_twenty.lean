-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_prepared_candidates_le_twenty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:46.163561+00:00
-- url     : https://prove2.me/submissions/81899465-6468-4a32-9356-6d2e228f8e8c

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_candidates_card_le_twenty
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_support_card_le_six
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















/-- Before the full final check, at most twenty candidates survive the
early checks and recovery on a well-formed typed input. -/
theorem p2m_local_recoh_cyclic_prepared_candidates_le_twenty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hformat : RecohCyclicInputFormat q entries terms) :
    (recohPreparedFastCandidates (recohTypedSquareSupport entries) (recohProductHalf q)
      (recohIndexedRecoverSupport (recohProductTwoCoordinates q)
        (recohCoefficientSignBools Sum.inl (recohCyclicBankPrime q)
          (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms))
      (recohEarlyCandidateCheck (recohTypedSquareSupport entries)
        (recohTypedSquareValue entries) (recohCyclicBankPrime q)
        (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms)).card ≤ 20 := by
  apply recoh_prepared_fast_candidates_card_le_twenty
  exact recoh_typed_square_support_card_le_six entries hformat.2.2.1

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohCyclicBankIndex d q → Couret.STROBO2TORS.RecohSparseTerms),
  @Couret.STROBO2TORS.RecohCyclicInputFormat d q inst entries terms →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (@Couret.STROBO2TORS.recohPreparedFastCandidates.{0} ((i : Fin d) → ZMod (q i))
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
            @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
          (fun a b =>
            @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
              (Fin.fintype d) a b)
          (@Couret.STROBO2TORS.recohTypedSquareSupport.{0} ((i : Fin d) → ZMod (q i))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            entries)
          (@Couret.STROBO2TORS.recohProductHalf d q)
          (@Couret.STROBO2TORS.recohIndexedRecoverSupport.{0, 0} ((i : Fin d) → ZMod (q i))
            (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Couret.STROBO2TORS.recohProductTwoCoordinates d q inst)
            (@Couret.STROBO2TORS.recohCoefficientSignBools.{0, 0, 0} ((i : Fin d) → ZMod (q i))
              (Sum.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                (@Couret.STROBO2TORS.RecohActiveTernaryCoordinate d q))
              (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
              (@Sum.inl.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
                (@Couret.STROBO2TORS.RecohActiveTernaryCoordinate d q))
              (@Couret.STROBO2TORS.recohCyclicBankPrime d q) (@Couret.STROBO2TORS.recohCyclicBankDepth d q inst)
              (@Couret.STROBO2TORS.recohCyclicBankEncoding d q) terms))
          (@Couret.STROBO2TORS.recohEarlyCandidateCheck.{0, 0, 0} ((i : Fin d) → ZMod (q i))
            (@Couret.STROBO2TORS.RecohEvenCoordinate d q) (@Couret.STROBO2TORS.RecohActiveTernaryCoordinate d q)
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Subtype.fintype.{0} (Fin d)
              (fun i =>
                @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
              (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
              (Fin.fintype d))
            (@Subtype.fintype.{0} (Fin d)
              (fun i =>
                And (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q i))
                  (@Exists.{1} (Fin d) fun j =>
                    @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q j)))
              (fun a =>
                @instDecidableAnd
                  (@Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q a))
                  (@Exists.{1} (Fin d) fun j =>
                    @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q j))
                  (Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (q a))
                  (@Nat.decidableExistsFin d
                    (fun j =>
                      @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q j))
                    fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a)))
              (Fin.fintype d))
            (@Couret.STROBO2TORS.recohTypedSquareSupport.{0} ((i : Fin d) → ZMod (q i))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              entries)
            (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              entries)
            (@Couret.STROBO2TORS.recohCyclicBankPrime d q) (@Couret.STROBO2TORS.recohCyclicBankDepth d q inst)
            (@Couret.STROBO2TORS.recohCyclicBankEncoding d q) terms)))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_prepared_candidates_le_twenty

