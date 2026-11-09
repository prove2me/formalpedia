-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_cyclic_bank_encoding_interpret
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:15.239788+00:00
-- url     : https://prove2.me/submissions/7b938a46-03d6-4036-bd01-657375e5e08e

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



















theorem p2m_local_recoh_cyclic_bank_encoding_interpret (i : RecohCyclicBankIndex q)
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    ((recohCyclicBankEncoding q i S).map (recohCyclicBankRoot q i ^ ·)).sum =
      recohSupportProbe (recohCyclicObservedBank q i) S := by
  cases i with
  | inl j => exact recoh_cyclic_primary_bank_interpret q 2 (recohCanonicalPrimaryData q 2) j S
  | inr j =>
    exact recoh_cyclic_primary_bank_interpret q 3 (recohCanonicalPrimaryData q 3)
      ⟨j.val, j.property.1⟩ S































end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (i : @Couret.STROBO2TORS.RecohCyclicBankIndex d q) (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
  @Eq.{1} Complex
    (@List.sum.{0} Complex Complex.instAdd Complex.instZero
      (@List.map.{0, 0} Nat Complex
        (fun x =>
          @HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
            (@Couret.STROBO2TORS.recohCyclicBankRoot d q inst i) x)
        (@Couret.STROBO2TORS.recohCyclicBankEncoding d q i S)))
    (@Couret.STROBO2TORS.recohSupportProbe.{0} ((i : Fin d) → ZMod (q i))
      (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
        @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
      (@Couret.STROBO2TORS.recohCyclicObservedBank d q inst i) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_cyclic_bank_encoding_interpret

