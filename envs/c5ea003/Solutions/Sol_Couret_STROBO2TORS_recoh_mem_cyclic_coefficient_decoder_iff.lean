-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_mem_cyclic_coefficient_decoder_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:54.958103+00:00
-- url     : https://prove2.me/submissions/8aa75f2d-cba6-4230-8fce-4d36cd5ec3d7

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_coefficient_decoder_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_input_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
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









































/-- Invalid typed input is rejected deterministically. -/
theorem recoh_cyclic_coefficient_decoder_rejects
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (hformat : ¬ RecohCyclicInputFormat q entries terms) :
    recohCyclicCoefficientDecoder q entries terms = ∅ := by
  simp only [recohCyclicCoefficientDecoder]
  rw [if_neg (fun h => hformat ((recoh_cyclic_input_check_iff q entries terms).mp h))]

/-- The input representation, all auxiliary constructions and the exact
output contract are linked in one theorem, with no semantic input witnesses. -/
theorem p2m_local_recoh_mem_cyclic_coefficient_decoder_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    S ∈ recohCyclicCoefficientDecoder q entries terms ↔
      RecohCyclicInputFormat q entries terms ∧ S.card = 3 ∧
        recohObservation (recohCyclicObservedBank q) S = recohCyclicTypedObservation q entries terms := by
  by_cases hformat : RecohCyclicInputFormat q entries terms
  · rw [recoh_cyclic_coefficient_decoder_eq_exact q entries terms hformat,
      recoh_mem_exact_decoder_iff]
    simp only [hformat, true_and]
  · rw [recoh_cyclic_coefficient_decoder_rejects q entries terms hformat]
    simp [hformat]







end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohCyclicBankIndex d q → Couret.STROBO2TORS.RecohSparseTerms)
  (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  Iff
    (@Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i))) (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
        (Finset.{0} ((i : Fin d) → ZMod (q i))) (@Finset.instSetLike.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))))
      (@Couret.STROBO2TORS.recohCyclicCoefficientDecoder d q inst entries terms) S)
    (And (@Couret.STROBO2TORS.RecohCyclicInputFormat d q inst entries terms)
      (And
        (@Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Eq.{1}
          (Prod.{0, 0} (((i : Fin d) → ZMod (q i)) → Nat) (@Couret.STROBO2TORS.RecohCyclicBankIndex d q → Complex))
          (@Couret.STROBO2TORS.recohObservation.{0, 0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Couret.STROBO2TORS.RecohCyclicBankIndex d q) (@Couret.STROBO2TORS.recohCyclicObservedBank d q inst) S)
          (@Couret.STROBO2TORS.recohCyclicTypedObservation d q inst entries terms)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_mem_cyclic_coefficient_decoder_iff

