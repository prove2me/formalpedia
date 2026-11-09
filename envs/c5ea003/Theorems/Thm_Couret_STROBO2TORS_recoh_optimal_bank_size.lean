-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_optimal_bank_size
-- name    : Couret.STROBO2TORS.recoh_optimal_bank_size
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:45.728606+00:00
-- url     : https://prove2.me/theorems/e36502ef-19bf-42af-a75a-b3ea9ef43f4f
-- title:
--   Optimal fixed character-bank size
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Assume $|G[2]|=2^r$, $|G[3]|=3^s$, and $|G|\ge3$. Define $b=0$ if $r=0$ and $b=r+s$ otherwise. Then
--
--   $$\exists\text{ a bank of }b\text{ characters making }\operatorname{Obs}\text{ injective on triples},$$
--
--   and every bank of $k<b$ characters fails injectivity. This determines the optimal size of a single fixed bank for all supports.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohOptimalBank.lean, lines 88–116; source file SHA-256 eefa340afa430ea5481039b5dcc716ba178daf20a3ab3a669e9ff87e2565a8d5; theorem Couret.STROBO2TORS.recoh_optimal_bank_size

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_bank_rank_sum
import Theorems.Thm_Couret_STROBO2TORS_recoh_exists_reconstructing_empty_bank
import Theorems.Thm_Couret_STROBO2TORS_recoh_no_short_reconstructing_bank
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
The optimal size of a fixed bank of individual, labelled complex
Fourier coefficients, given the labelled ordered convolution square of a
three-element support.  Zero is allowed in the support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]

theorem recoh_optimal_bank_size
    (r s : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) :
    (∃ bank : Fin (recohOptimalBudget r s) → AddChar G ℂ,
      Function.Injective (fun S : {S : Finset G // S.card = 3} =>
        recohObservation bank S.1)) ∧
    (∀ k : ℕ, k < recohOptimalBudget r s →
      ∀ bank : Fin k → AddChar G ℂ,
        ¬ Function.Injective (fun S : {S : Finset G // S.card = 3} =>
          recohObservation bank S.1)) := by sorry


end Couret.STROBO2TORS
