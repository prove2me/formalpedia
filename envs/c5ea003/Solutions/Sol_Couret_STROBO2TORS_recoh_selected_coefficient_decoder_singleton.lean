-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_selected_coefficient_decoder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:32.725669+00:00
-- url     : https://prove2.me/submissions/cb659cae-224c-41a1-8af4-62c3ac6381da

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

























































/-- Any valid observation of a triple is decoded uniquely using its actual
square-selected bank, with no unmeasured ternary values in the input. -/
theorem p2m_local_recoh_selected_coefficient_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohSelectedBankIndex q entries → RecohSparseTerms)
    (hformat : RecohSelectedInputFormat q entries terms)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hobs : recohObservation (recohSelectedObservedBank q entries) S =
      recohSelectedTypedObservation q entries terms) :
    recohSelectedCoefficientDecoder q entries terms = {S} := by
  ext T
  constructor
  · intro hT
    have ht := (recoh_mem_selected_coefficient_decoder_iff q entries terms T).mp hT
    apply Finset.mem_singleton.mpr
    exact recoh_selected_observation_injective_on_square q entries T S ht.2.1 hS
      (congrArg Prod.fst ht.2.2) (congrArg Prod.fst hobs) (ht.2.2.trans hobs.symm)
  · intro hT
    rw [Finset.mem_singleton] at hT
    rw [hT]
    exact (recoh_mem_selected_coefficient_decoder_iff q entries terms S).mpr
      ⟨hformat, hS, hobs⟩



end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms),
  @Couret.STROBO2TORS.RecohSelectedInputFormat d q inst entries terms →
    ∀ (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
      @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @Eq.{1}
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
            (@Couret.STROBO2TORS.recohSelectedTypedObservation d q inst entries terms) →
          @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
            (@Couret.STROBO2TORS.recohSelectedCoefficientDecoder d q inst entries terms)
            (@Singleton.singleton.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
              (@Finset.instSingleton.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_selected_coefficient_decoder_singleton

