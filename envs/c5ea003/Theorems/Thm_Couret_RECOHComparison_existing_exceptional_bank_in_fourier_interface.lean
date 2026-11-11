-- Prove2me | Theorems.Thm_Couret_RECOHComparison_existing_exceptional_bank_in_fourier_interface
-- name    : Couret.RECOHComparison.existing_exceptional_bank_in_fourier_interface
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:03:51.938758+00:00
-- url     : https://prove2.me/theorems/88f4e0f7-b5e9-401b-877e-3851fe85a5d7
-- title:
--   An exceptional square fibre admits an r plus one Fourier bank
-- statement:
--   Let $G$ be a finite abelian group with decidable equality and $|G[2]|=2^r$. Let $S\subseteq G$ have three elements, and suppose its square fibre has the exceptional cardinality
--
--   $$|\operatorname{squareFibre}(S)|=2|G[2]|.$$
--
--   There exists a bank $(\chi_i)_{i\in\operatorname{Fin}(r+1)}$ of complex additive characters for which
--
--   $$T\longmapsto\bigl(i\longmapsto\operatorname{recohFourierSum}(\chi_i,T)\bigr)$$
--
--   is injective on $\operatorname{squareFibre}(S)$. The bank may depend on $S$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/6cbb19a17462c6db22ebf84a5140f2a904bafd84/research/strobo-2tors-2026-10-12/lean/RecohBranchComparison.lean#L46-L56; source SHA-256 d7710d121efd743a6a2abf20367e2a96184cf99167f1921858f6ee57e7485dbc; theorem Couret.RECOHComparison.existing_exceptional_bank_in_fourier_interface

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_exceptional_fibre
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

theorem existing_exceptional_bank_in_fourier_interface (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (S : Finset G) (hS : S.card = 3)
    (hexceptional : (squareFibre S).card = 2 * (twoTorsion : Finset G).card) :
    ∃ bank : Fin (r + 1) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohFourierSum (bank i) T)
        (squareFibre S) := by sorry




end Couret.RECOHComparison
