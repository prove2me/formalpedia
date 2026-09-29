-- Prove2me | Theorems.Thm_B3Free_exists_base_and_atoms
-- name    : B3Free.exists_base_and_atoms
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:13:07.202536+00:00
-- url     : https://prove2.me/theorems/1984fec5-3251-4f5b-9ab1-e079f0ae1172
-- title:
--   Inside any set `C` with `a + d ≤ |C|` one finds a base set of size `a` together with
-- statement:
--   Inside any set `C` with `a + d ≤ |C|` one finds a base set of size `a` together with
--   `d` further elements of `C` outside it.
--
--   ```lean
--   theorem B3Free.exists_base_and_atoms{a : ℕ} {C : Finset α} (h : a + d ≤ C.card) :
--       ∃ (s : Finset α) (f : Fin d → α), Function.Injective f ∧ (∀ i, f i ∉ s) ∧
--         s.card = a ∧ s ⊆ C ∧ ∀ i, f i ∈ C := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/B3FreeFamiliesBounds.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/B3FreeFamiliesBounds.lean#L117

-- Thm stub generated from Bridges/B3FreeFamiliesBounds.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
import Definitions.Def_Bridges_B3FreeFamiliesBounds
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Maximality of layer families, exact values, and a general upper bound for `La(n, B_d)`

This file continues `Catalog/Bridges/B3FreeFamilies.lean`, which sets up the framework of
weak/strong `P`-free families surrounding the paper *On the maximum size of `B_3`-free
families*.

## Main results

* `not_strongFree_insert_layers`, `layers_maximal_weakFree`, `layers_maximal_strongFree` —
  **maximality of the layer construction**: adding to `d` consecutive layers any set whose
  size lies outside the corresponding interval creates a strong (hence weak) copy of `B_d`.
  Consequently an `ε`-improvement can never be obtained by enlarging the layer family.
* `La_boolLat_eq_of_card_eq_succ`, `LaStar_boolLat_eq_of_card_eq_succ`, `La_boolLat3_fin4` —
  the exact value `La(d+1, B_d) = La*(d+1, B_d) = 2^(d+1) - 2`, attained by the `d` layers
  `1, …, d`; in particular `La(4, B_3) = 14`.  Hence `La` and `La*` agree for `n ∈ {d, d+1}`
  (`La_eq_LaStar_of_card_eq_succ`).
* `La_boolLat_lt_succ_of_card_eq_succ`, `La_boolLat3_lt_boolLat4_fin4` — strict
  monotonicity `La(d+1, B_d) < La(d+1, B_(d+1))`.
* `not_hasChain_of_weakFree`, `card_le_of_not_hasChain`, `La_boolLat_le` — a chain of
  `2^d` sets contains a weak copy of `B_d`, and a Mirsky-type peeling of maximal sets
  combined with Sperner's theorem gives the **general upper bound**
  `La(n, B_d) ≤ (2^d - 1) · C(n, ⌊n/2⌋)`; for `d = 3` this brackets the paper's quantity,
  `3 · C(n, ⌊n/2⌋-2) ≤ La(n, B_3) ≤ 7 · C(n, ⌊n/2⌋)` (`La_boolLat3_bounds`).
-/


open B3Free

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

/-! ## Maximality of the layer families

The `d`-layer construction is not only weak `B_d`-free: it is a *maximal* such
family.  Adding any further set to `layers α a d` creates a strong (hence also a
weak) copy of `B_d`.  So the `ε`-improvement of Ellis–Ivan–Leader (and of the
`B_3` paper) can never be obtained by enlarging the layer family; sets have to be
deleted first.
-/


variable {d : ℕ}



omit [Fintype α] in

theorem B3Free.exists_base_and_atoms{a : ℕ} {C : Finset α} (h : a + d ≤ C.card) :
    ∃ (s : Finset α) (f : Fin d → α), Function.Injective f ∧ (∀ i, f i ∉ s) ∧
      s.card = a ∧ s ⊆ C ∧ ∀ i, f i ∈ C := by sorry
