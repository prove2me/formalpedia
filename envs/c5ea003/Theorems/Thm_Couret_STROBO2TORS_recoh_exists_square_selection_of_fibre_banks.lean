-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exists_square_selection_of_fibre_banks
-- name    : Couret.STROBO2TORS.recoh_exists_square_selection_of_fibre_banks
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:09.190059+00:00
-- url     : https://prove2.me/theorems/b93568f5-d2b7-436a-9862-fc9a897a7ac6
-- title:
--   Fibrewise character banks can be selected from the square alone
-- statement:
--   Let $G$ be an abelian group, $R_S(z)$ the ordered pair-sum count of a support $S$, $P_\chi(S)=\sum_{s\in S}\chi(s)$, and $F(S)=\{T:|T|=3,R_T=R_S\}$. Put $H=G[2]$. Assume $G$ finite. Fix $k\in\mathbb N$ and suppose every triple $S$ admits a $k$-character bank separating $F(S)$. There is a selection $\sigma$ assigning a $k$-character bank to each function $R:G\to\mathbb N$ such that
--
--   $$S\longmapsto(R_S,(P_{\sigma(R_S)_i}(S))_{i<k})\quad\text{is injective on triples}.$$
--
--   The selection is existential and depends only on the observed square.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreOptimal.lean, lines 150–195; source file SHA-256 609b61fbff59a0b55eb1cdb79538dc43bc1d0ed28d4633216dc67d9b09fe3bac; theorem Couret.STROBO2TORS.recoh_exists_square_selection_of_fibre_banks

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

theorem recoh_exists_square_selection_of_fibre_banks (k : ℕ)
    (hbank : ∀ S : Finset G, S.card = 3 → ∃ bank : Fin k → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre S)) :
    ∃ select : (G → ℕ) → (Fin k → AddChar G ℂ),
      Function.Injective (fun S : {S : Finset G // S.card = 3} =>
        recohSquareSelectedObservation select S.1) := by sorry














end Couret.STROBO2TORS
