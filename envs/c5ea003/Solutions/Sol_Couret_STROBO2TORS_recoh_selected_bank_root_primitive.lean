-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_selected_bank_root_primitive
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:44.062478+00:00
-- url     : https://prove2.me/submissions/eda73cdb-530b-48b3-89c2-98ed76c1d3ef

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



























theorem p2m_local_recoh_selected_bank_root_primitive
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (i : RecohSelectedBankIndex q entries) :
    IsPrimitiveRoot (recohSelectedBankRoot q entries i)
      ((recohSelectedBankPrime q entries i) ^ (recohSelectedBankDepth q entries i + 1)) := by
  cases i with
  | inl j => exact recoh_cyclic_root_primitive _
  | inr j => exact recoh_cyclic_root_primitive _

































end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (i : @Couret.STROBO2TORS.RecohSelectedBankIndex d q inst entries),
  @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing)
    (@Couret.STROBO2TORS.recohSelectedBankRoot d q inst entries i)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
      (@Couret.STROBO2TORS.recohSelectedBankPrime d q inst entries i)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Couret.STROBO2TORS.recohSelectedBankDepth d q inst entries i)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_selected_bank_root_primitive

