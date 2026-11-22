-- Prove2me | Theorems.Thm_infinite_ramsey_seq
-- name    : infinite_ramsey_seq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:10.287338+00:00
-- url     : https://prove2.me/theorems/dde83d62-a9d5-49e5-97c6-cc34ac0a98fe
-- title:
--   infinite ramsey seq: infinite ramsey seq
-- statement:
--   The infinite ramsey seq construction uses the infinite ramsey seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L145-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L145-L151

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

theorem infinite_ramsey_seq [Finite κ] (r : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = r → c t = col := by sorry
