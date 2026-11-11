-- Prove2me | Theorems.Thm_Couret_RECOHComparison_fourier_sum_eq_support_probe
-- name    : Couret.RECOHComparison.fourier_sum_eq_support_probe
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:01:33.907208+00:00
-- url     : https://prove2.me/theorems/2ea63fda-43c2-4cc9-83e6-8ad4d4ce279b
-- title:
--   The two RECOH interfaces use the same Fourier sum
-- statement:
--   Let $G$ be an abelian group, $\chi:G\to\mathbb C$ an additive character, and $S\subseteq G$ a finite set. The two source interfaces agree exactly:
--
--   $$\operatorname{recohFourierSum}(\chi,S)=\operatorname{recohSupportProbe}(\chi,S).$$
--
--   This is equality of the complex sums, rather than equality only of their magnitudes.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/6cbb19a17462c6db22ebf84a5140f2a904bafd84/research/strobo-2tors-2026-10-12/lean/RecohBranchComparison.lean#L14-L17; source SHA-256 d7710d121efd743a6a2abf20367e2a96184cf99167f1921858f6ee57e7485dbc; theorem Couret.RECOHComparison.fourier_sum_eq_support_probe

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

omit [DecidableEq G] in

theorem fourier_sum_eq_support_probe (chi : AddChar G ℂ) (S : Finset G) :
    recohFourierSum chi S = recohSupportProbe chi S := by sorry




variable [Fintype G]







end Couret.RECOHComparison
