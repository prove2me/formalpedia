-- Prove2me | Theorems.Thm_Couret_RECOHComparison_binary_bank_discharges_orbit_hypotheses
-- name    : Couret.RECOHComparison.binary_bank_discharges_orbit_hypotheses
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:05:29.383867+00:00
-- url     : https://prove2.me/theorems/c180163d-f998-4566-bbc1-6788a273b766
-- title:
--   A binary character bank separates translations within each triple orbit
-- statement:
--   Let $G$ be a finite abelian group with decidable equality, and let $r\in\mathbb N$ satisfy $|G[2]|=2^r$, where $G[2]=\{u:2u=0\}$. There exists a bank $(\chi_i)_{i\in\operatorname{Fin}(r)}$ of complex additive characters such that, for every three-element support $S$ and all $u,v\in G[2]$,
--
--   $$\bigl(\forall i,\;\operatorname{recohFourierSum}(\chi_i,S+u)=\operatorname{recohFourierSum}(\chi_i,S+v)\bigr)\Longrightarrow u=v.$$
--
--   The conclusion concerns translations of the same support within one two-torsion orbit.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/6cbb19a17462c6db22ebf84a5140f2a904bafd84/research/strobo-2tors-2026-10-12/lean/RecohBranchComparison.lean#L26-L44; source SHA-256 d7710d121efd743a6a2abf20367e2a96184cf99167f1921858f6ee57e7485dbc; theorem Couret.RECOHComparison.binary_bank_discharges_orbit_hypotheses

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
import Theorems.Thm_Couret_RECOHComparison_actual_probe_covariance
import Theorems.Thm_Couret_RECOHComparison_fourier_sum_eq_support_probe
import Theorems.Thm_Couret_STROBO2TORS_recoh_orbit_translation_separated
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
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

theorem binary_bank_discharges_orbit_hypotheses (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r) :
    ∃ bank : Fin r → AddChar G ℂ,
      ∀ S : Finset G, S.card = 3 → ∀ u v : G,
        u + u = 0 → v + v = 0 →
        (∀ i, recohFourierSum (bank i) (translateSupport S u) =
          recohFourierSum (bank i) (translateSupport S v)) → u = v := by sorry






end Couret.RECOHComparison
