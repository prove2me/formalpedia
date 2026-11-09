-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_bank_encoding_length
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:12.135236+00:00
-- url     : https://prove2.me/submissions/9d2c1a78-e4c4-4200-9597-dd6bee92e3b5

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_exponents_length
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





















omit [∀ i, NeZero (q i)] in
theorem p2m_local_recoh_cyclic_bank_encoding_length (i : RecohCyclicBankIndex q)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    (recohCyclicBankEncoding q i S).length = S.card := by
  cases i with
  | inl j => exact recoh_cyclic_exponents_length q j.val S
  | inr j => exact recoh_cyclic_exponents_length q j.val S





























end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat) (i : @Couret.STROBO2TORS.RecohCyclicBankIndex d q)
  (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Nat (@List.length.{0} Nat (@Couret.STROBO2TORS.recohCyclicBankEncoding d q i S))
    (@Finset.card.{0} ((i : Fin d) → ZMod (q i)) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_bank_encoding_length

