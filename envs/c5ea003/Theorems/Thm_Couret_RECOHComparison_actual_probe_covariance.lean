-- Prove2me | Theorems.Thm_Couret_RECOHComparison_actual_probe_covariance
-- name    : Couret.RECOHComparison.actual_probe_covariance
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:03:18.619782+00:00
-- url     : https://prove2.me/theorems/c92ad487-6f54-451e-be26-3c0d6d443a51
-- title:
--   Translation covariance in the RECOH Fourier interface
-- statement:
--   Let $G$ be an abelian group with decidable equality, $\chi:G\to\mathbb C$ an additive character, $S\subseteq G$ finite, and $u\in G$. With the source's translation convention,
--
--   $$\operatorname{recohFourierSum}(\chi,\operatorname{translateSupport}(S,u))=\chi(u)\operatorname{recohFourierSum}(\chi,S).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/6cbb19a17462c6db22ebf84a5140f2a904bafd84/research/strobo-2tors-2026-10-12/lean/RecohBranchComparison.lean#L19-L22; source SHA-256 d7710d121efd743a6a2abf20367e2a96184cf99167f1921858f6ee57e7485dbc; theorem Couret.RECOHComparison.actual_probe_covariance

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
import Theorems.Thm_Couret_RECOHComparison_fourier_sum_eq_support_probe
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

theorem actual_probe_covariance (chi : AddChar G ℂ) (S : Finset G) (u : G) :
    recohFourierSum chi (translateSupport S u) = chi u * recohFourierSum chi S := by sorry


variable [Fintype G]







end Couret.RECOHComparison
