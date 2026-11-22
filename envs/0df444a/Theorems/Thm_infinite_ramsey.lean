-- Prove2me | Theorems.Thm_infinite_ramsey
-- name    : infinite_ramsey
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:10.371623+00:00
-- url     : https://prove2.me/theorems/06feb6b9-13ec-4218-af01-6a1fd5efc1b8
-- title:
--   infinite ramsey: infinite ramsey
-- statement:
--   The infinite ramsey construction uses the infinite ramsey property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L59-L143
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L59-L143

module
public import Mathlib.Data.Finset.Card
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
variable {κ : Type*}

theorem infinite_ramsey [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by sorry
