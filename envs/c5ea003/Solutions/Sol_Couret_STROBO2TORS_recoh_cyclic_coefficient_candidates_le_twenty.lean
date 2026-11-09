-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_coefficient_candidates_le_twenty
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:53:43.159098+00:00
-- url     : https://prove2.me/submissions/315e6e65-7953-4fcf-8a8c-01566f07c9cb

import Aesop
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_fast_candidates_card_le_twenty
import Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_support_card_le_six
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
import Definitions.Def_Couret_RecohCyclicPrimaryBank_92b8732c410a

set_option autoImplicit false

/-!
An instantiated RECOH decoder on typed observations of cyclic products.

The user supplies only the moduli, labelled square entries, and the observed
coefficient lists.  The primary parameters, exponent encoders, binary
coordinates, doubling solver, square-value function and its covering set
are constructed here.  Their correctness contracts are all discharged.

There is one binary slot for every even factor. Ternary slots occur only
when some factor is even, exactly as for the fixed bank in the Python
decoder. The input guard also imposes moduli at least two, group order at
least three, and the typed numeric/uniqueness checks of its observation
readers. JSON syntax, machine execution and serialization remain separate.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

















































/-- Before the final filter, valid input yields at most twenty recovered
candidates. This is a cardinality bound, not a bit-complexity theorem. -/
theorem p2m_local_recoh_cyclic_coefficient_candidates_le_twenty
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hformat : RecohCyclicInputFormat q entries terms) :
    (recohFastCandidates (recohTypedSquareSupport entries) (recohProductHalf q)
      (recohIndexedRecoverSupport (recohProductTwoCoordinates q)
        (recohCoefficientSignBools Sum.inl (recohCyclicBankPrime q)
          (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms))).card ≤ 20 := by
  apply recoh_fast_candidates_card_le_twenty
  exact recoh_typed_square_support_card_le_six entries hformat.2.2.1

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohCyclicBankIndex d q → Couret.STROBO2TORS.RecohSparseTerms),
  @Couret.STROBO2TORS.RecohCyclicInputFormat d q inst entries terms →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (@Couret.STROBO2TORS.recohFastCandidates.{0} ((i : Fin d) → ZMod (q i))
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
              (@Couret.STROBO2TORS.recohCyclicBankEncoding d q) terms))))
      (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_coefficient_candidates_le_twenty

