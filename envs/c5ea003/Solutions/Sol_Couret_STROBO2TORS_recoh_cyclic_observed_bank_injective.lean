-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_observed_bank_injective
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:44:30.470783+00:00
-- url     : https://prove2.me/submissions/10bae9c8-8846-4211-9aea-f576b68ae1df

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_primary_observation_injective
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_injective_of_trivial_two_torsion
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























/-- The conditional bank reconstructs triples also in the odd-order case,
where it has no slots and the square alone is injective. -/
theorem p2m_local_recoh_cyclic_observed_bank_injective :
    Function.Injective (fun S :
      {S : Finset ((i : Fin d) → ZMod (q i)) // S.card = 3} =>
      recohObservation (recohCyclicObservedBank q) S.1) := by
  intro S T hobs
  by_cases heven : ∃ j : Fin d, 2 ∣ q j
  · apply recoh_cyclic_primary_observation_injective q
      (recohCanonicalPrimaryData q 2) (recohCanonicalPrimaryData q 3)
    apply Prod.ext
    · change orderedSquare S.1 = orderedSquare T.1
      exact congrArg Prod.fst hobs
    · funext i
      cases i with
      | inl j => exact congrFun (congrArg Prod.snd hobs) (Sum.inl j)
      | inr j =>
        exact congrFun (congrArg Prod.snd hobs)
          (Sum.inr ⟨j.val, j.property, heven⟩)
  · apply recoh_square_injective_of_trivial_two_torsion
    · intro u hu
      funext i
      have hcop : Nat.Coprime 2 (q i) :=
        Nat.prime_two.coprime_iff_not_dvd.mpr (fun hi => heven ⟨i, hi⟩)
      apply recoh_cyclic_torsion_zero_of_coprime 2 (q i) hcop (u i)
      simpa only [two_nsmul, Pi.add_apply, Pi.zero_apply] using congrFun hu i
    · exact congrArg Prod.fst hobs



























end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)],
  @Function.Injective.{1, 1}
    (@Subtype.{1} (Finset.{0} ((i : Fin d) → ZMod (q i))) fun S =>
      @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (Prod.{0, 0} (((i : Fin d) → ZMod (q i)) → Nat) (@Couret.STROBO2TORS.RecohCyclicBankIndex d q → Complex)) fun S =>
    @Couret.STROBO2TORS.recohObservation.{0, 0} ((i : Fin d) → ZMod (q i))
      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
      (fun a b =>
        @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
          (Fin.fintype d) a b)
      (@Couret.STROBO2TORS.RecohCyclicBankIndex d q) (@Couret.STROBO2TORS.recohCyclicObservedBank d q inst)
      (@Subtype.val.{1} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (fun S =>
          @Eq.{1} Nat (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_observed_bank_injective

