-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_optimal_fibre_bank_size
-- name    : Couret.STROBO2TORS.recoh_optimal_fibre_bank_size
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:29.369618+00:00
-- url     : https://prove2.me/theorems/f9f31597-e85a-4e45-808d-70bcce151cc0
-- title:
--   The optimal bank size equals the binary logarithm of the square fibre
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Assume $G$ finite, $|H|=2^r$, and $|S|=3$. Set $b=\lfloor\log_2|F(S)|\rfloor$. Then
--
--   $$\exists\chi_0,\ldots,\chi_{b-1}\text{ separating }F(S),$$
--   $$k<b\Longrightarrow\text{no bank of }k\text{ complex additive characters separates }F(S).$$
--
--   For triples the fibre size is a power of two, so this logarithm is exact.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreOptimal.lean, lines 51–76; source file SHA-256 609b61fbff59a0b55eb1cdb79538dc43bc1d0ed28d4633216dc67d9b09fe3bac; theorem Couret.STROBO2TORS.recoh_optimal_fibre_bank_size

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_double_fibre_rank_succ_le_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_exceptional_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_ordinary_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_budget_exceptional
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_budget_ordinary
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_rank_le_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_card_eq_nat_card
import Theorems.Thm_Couret_STROBO2TORS_squareFibre_card_h_or_two_h
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

theorem recoh_optimal_fibre_bank_size (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (S : Finset G) (hS : S.card = 3) :
    (∃ bank : Fin (recohFibreBudget S) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S)) ∧
    (∀ k : ℕ, k < recohFibreBudget S → ∀ bank : Fin k → AddChar G ℂ,
      ¬ Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S)) := by sorry


























end Couret.STROBO2TORS
