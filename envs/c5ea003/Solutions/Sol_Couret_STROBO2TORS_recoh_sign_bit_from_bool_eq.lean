-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_sign_bit_from_bool_eq
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:41:03.916093+00:00
-- url     : https://prove2.me/submissions/18476690-0f60-4667-857a-737a44915bf2

import Aesop
import Definitions.Def_Couret_RecohExactSignBackend_8d2941f5c2c9
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Computable comparison bits and their refinement of complex sign recovery.

The comparison booleans are supplied by an exact arithmetic backend.  Only
their correctness proposition mentions complex numbers.  The recovered
coordinate vector and transport through a supplied coordinate equivalence
are ordinary Lean definitions, with no complex equality decision at runtime.
-/

namespace Couret.STROBO2TORS



theorem p2m_local_recoh_sign_bit_from_bool_eq (base obs : ℂ) (same : Bool)
    (h : same = true ↔ obs = base) :
    recohSignBitFromBool same = recohRecoveredSignBit base obs := by
  classical
  cases same <;> simp_all [recohSignBitFromBool, recohRecoveredSignBit]

variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2







variable [DecidableEq G]





























end Couret.STROBO2TORS


theorem solution : ∀ (base obs : Complex) (same : Bool),
  Iff (@Eq.{1} Bool same Bool.true) (@Eq.{1} Complex obs base) →
    @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Couret.STROBO2TORS.recohSignBitFromBool same) (Couret.STROBO2TORS.recohRecoveredSignBit base obs) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_sign_bit_from_bool_eq

