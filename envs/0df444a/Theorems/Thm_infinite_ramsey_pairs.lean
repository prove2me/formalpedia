-- Prove2me | Theorems.Thm_infinite_ramsey_pairs
-- name    : infinite_ramsey_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:01.014844+00:00
-- url     : https://prove2.me/theorems/e17f3c5c-f192-441b-9a05-63945f31e705
-- title:
--   infinite ramsey pairs: infinite ramsey pairs
-- statement:
--   **The infinite Ramsey theorem for pairs (RT²)**, in relational form: for a finite colouring
--   `c` of the ordered pairs `m < n`, there is a strictly monotone `e` and a colour `k` with
--   `c (e i) (e j) = k` for all `i < j`. Derived from `infinite_ramsey_seq` at arity `2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L156-L202
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L156-L202

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

theorem infinite_ramsey_pairs {κ : Type*} [Finite κ] (c : ∀ (m n : ℕ), m < n → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ i j : ℕ, (h : i < j) → c (e i) (e j) (he h) = k := by sorry
