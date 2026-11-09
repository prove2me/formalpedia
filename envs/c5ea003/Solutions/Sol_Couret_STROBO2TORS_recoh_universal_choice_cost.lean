-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_universal_choice_cost
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:30.114422+00:00
-- url     : https://prove2.me/submissions/00a08c91-62f1-4c30-b644-c67feb770897

import Aesop
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
Optimal character banks selected from the observed labelled ordered square.
The selected bank is fixed on its entire fibre. Selection is existential;
this module does not implement selection from raw or typed decoder input.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

































/-- A fixed universal bank pays `s-1` extra slots when both torsion ranks
are positive. Both budgets refer to exact labelled complex coefficients. -/
theorem p2m_local_recoh_universal_choice_cost (r s : ℕ) (hr : 0 < r) (hs : 0 < s) :
    recohOptimalBudget r s - recohAfterSquareBudget r s = s - 1 := by
  have hr0 : r ≠ 0 := by omega
  have hs1 : 1 ≤ s := hs
  simp only [recohOptimalBudget, recohAfterSquareBudget, if_neg hr0,
    Nat.min_eq_left hs1]
  omega

end Couret.STROBO2TORS


theorem solution : ∀ (r s : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s →
      @Eq.{1} Nat
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (Couret.STROBO2TORS.recohOptimalBudget r s)
          (Couret.STROBO2TORS.recohAfterSquareBudget r s))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) s
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_universal_choice_cost

