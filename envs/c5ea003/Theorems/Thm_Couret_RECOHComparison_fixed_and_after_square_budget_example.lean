-- Prove2me | Theorems.Thm_Couret_RECOHComparison_fixed_and_after_square_budget_example
-- name    : Couret.RECOHComparison.fixed_and_after_square_budget_example
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:01:32.764658+00:00
-- url     : https://prove2.me/theorems/6a9b6e5e-c7a5-49ce-a667-10cfb177b6d6
-- title:
--   The fixed and after-square budgets differ at parameters one and two
-- statement:
--   At the source's parameters $(1,2)$, the two budget functions have the exact values
--
--   $$\operatorname{recohOptimalBudget}(1,2)=3\quad\text{and}\quad\operatorname{recohAfterSquareBudget}(1,2)=2.$$
--
--   This numerical comparison distinguishes the two budget formulas; it does not by itself classify any group.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/6cbb19a17462c6db22ebf84a5140f2a904bafd84/research/strobo-2tors-2026-10-12/lean/RecohBranchComparison.lean#L58-L61; source SHA-256 d7710d121efd743a6a2abf20367e2a96184cf99167f1921858f6ee57e7485dbc; theorem Couret.RECOHComparison.fixed_and_after_square_budget_example

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

theorem fixed_and_after_square_budget_example :
    recohOptimalBudget 1 2 = 3 ∧ recohAfterSquareBudget 1 2 = 2 := by sorry


end Couret.RECOHComparison
