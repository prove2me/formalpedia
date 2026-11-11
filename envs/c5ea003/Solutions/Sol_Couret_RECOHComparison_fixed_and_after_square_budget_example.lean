-- Prove2me | solution 1 for Couret.RECOHComparison.fixed_and_after_square_budget_example
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-10T13:01:38.300694+00:00
-- url     : https://prove2.me/submissions/8a6a54b2-4736-4d8c-bcaf-e18209657d84

import Aesop
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497
import Definitions.Def_Couret_RecohFourierCovarianceBridge_d0f4471a4239
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
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
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Definitions.Def_Couret_RecohFourierCovarianceBridge_d0f4471a4239
import Definitions.Def_Couret_RecohFibreOptimal_b9d6825ce497

set_option autoImplicit false

/-! Additive interoperability proof. Existing source statements are
unchanged. This does not merge PR96 or replace the executable selector of PR60. -/
namespace Couret.RECOHComparison
open Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]





/-- Concrete budget values distinguish the fixed-bank and after-square
models; this arithmetic example alone is not a group classification. -/
theorem p2m_local_fixed_and_after_square_budget_example :
    recohOptimalBudget 1 2 = 3 ∧ recohAfterSquareBudget 1 2 = 2 := by decide

end Couret.RECOHComparison

theorem solution : And
  (@Eq.{1} Nat
    (Couret.STROBO2TORS.recohOptimalBudget (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (@Eq.{1} Nat
    (Couret.STROBO2TORS.recohAfterSquareBudget (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) := @_root_.Couret.RECOHComparison.p2m_local_fixed_and_after_square_budget_example

