-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_no_short_square_selection
-- name    : Couret.STROBO2TORS.recoh_no_short_square_selection
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:54:26.225518+00:00
-- url     : https://prove2.me/theorems/71e8f671-2bc1-40d2-bb65-8063a33f881b
-- title:
--   Square-dependent selection cannot beat the after-square budget
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Assume $|G[2]|=2^r$, $|G[3]|=3^s$, and $|G|\ge3$. Put $b=0$ if $r=0$, and $b=r+\min(1,s)$ otherwise. For $k<b$, let any rule select a bank of $k$ characters from the full square function. Then
--
--   $$S\longmapsto\bigl(Q_S,(P_{\operatorname{select}(Q_S)_i}(S))_{i<k}\bigr)\text{ is not injective on three-element supports}.$$
--
--   This lower bound allows the bank to depend on the observed square.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohFibreOptimal.lean, lines 230–270; source file SHA-256 609b61fbff59a0b55eb1cdb79538dc43bc1d0ed28d4633216dc67d9b09fe3bac; theorem Couret.STROBO2TORS.recoh_no_short_square_selection

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_exceptional_fibre_of_positive_ranks
import Theorems.Thm_Couret_STROBO2TORS_recoh_fibre_card_le_two_pow_of_separating_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_square_selection_injective_on_fibre
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_card_eq_nat_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_card
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
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

theorem recoh_no_short_square_selection (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) (k : ℕ)
    (hk : k < recohAfterSquareBudget r s)
    (select : (G → ℕ) → (Fin k → AddChar G ℂ)) :
    ¬ Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohSquareSelectedObservation select S.1) := by sorry








end Couret.STROBO2TORS
