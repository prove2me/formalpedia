-- Prove2me | Theorems.Thm_infinite_ramsey_triples
-- name    : infinite_ramsey_triples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:12.493597+00:00
-- url     : https://prove2.me/theorems/eba63327-2649-489d-90aa-11a8cdb25754
-- title:
--   infinite ramsey triples: infinite ramsey triples
-- statement:
--   **The infinite Ramsey theorem for triples (RT³)**, in relational form, derived from
--   `infinite_ramsey_seq` at arity `3` (colour a `3`-subset by `c` of its least, middle and greatest
--   element).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L207-L293
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Ramsey/Infinite.lean#L207-L293

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

theorem infinite_ramsey_triples {κ : Type*} [Finite κ]
    (c : ∀ (m n l : ℕ), (m < n ∧ n < l) → κ) :
    ∃ (e : ℕ → ℕ), ∃ (he : StrictMono e), ∃ k : κ,
      ∀ h i j : ℕ, (hs : h < i ∧ i < j) →
        c (e h) (e i) (e j) ⟨he hs.1, he hs.2⟩ = k := by sorry
