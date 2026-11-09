-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exists_after_square_fibre_bank
-- name    : Couret.STROBO2TORS.recoh_exists_after_square_fibre_bank
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:21.905034+00:00
-- url     : https://prove2.me/theorems/e729e0f7-9b43-4b12-8807-f1acaadd47d6
-- title:
--   A small bank separates each fixed square fibre
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Assume $G$ finite, $|H|=2^r$ and $|K|=3^s$ for natural $r,s$, and $|S|=3$. There exists a bank of $b(r,s)$ characters whose readings are injective on $F(S)$, where $$b(r,s)=\begin{cases}0&r=0,\\r+\min(1,s)&r>0.\end{cases}$$
--
--   The bank may depend on $S$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreOptimal.lean, lines 117–141; source file SHA-256 609b61fbff59a0b55eb1cdb79538dc43bc1d0ed28d4633216dc67d9b09fe3bac; theorem Couret.STROBO2TORS.recoh_exists_after_square_fibre_bank

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_exceptional_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_bank_on_ordinary_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_bank_rank_sum
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_empty_bank
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

theorem recoh_exists_after_square_fibre_bank (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (S : Finset G) (hS : S.card = 3) :
    ∃ bank : Fin (recohAfterSquareBudget r s) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S) := by sorry


















end Couret.STROBO2TORS
