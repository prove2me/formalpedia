-- Prove2me | Theorems.Thm_B3Free_sum_choose_le_La
-- name    : B3Free.sum_choose_le_La
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:11:56.733917+00:00
-- url     : https://prove2.me/theorems/a5b7fd7c-f015-4a87-84a4-8167bf5d0281
-- title:
--   Lower bound from the layer construction: `La(n, B_d) ≥ ∑ᵢ C(n, i)` over any
-- statement:
--   **Lower bound from the layer construction**: `La(n, B_d) ≥ ∑ᵢ C(n, i)` over any
--   `d` consecutive layers.
--
--   ```lean
--   theorem B3Free.sum_choose_le_La(a d : ℕ) :
--       ∑ i ∈ Finset.Ico a (a + d), (Fintype.card α).choose i ≤ La α (BoolLat d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/B3FreeFamilies.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/B3FreeFamilies.lean#L324

-- Thm stub generated from Bridges/B3FreeFamilies.lean
import Mathlib
import Definitions.Def_Bridges_B3FreeFamilies
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Weak and strong `P`-free families and the layer number `e(P)`

This file formalizes the basic framework surrounding the paper
*On the maximum size of `B_3`-free families*, and proves the exact value of the
"number of free consecutive layers" invariant for the Boolean lattice posets `B_d`.

## Framework

Following the paper, a family `𝒢` of sets is a **weak copy** of a poset `P` if
there is a bijection `ι : P → 𝒢` with `ι p ⊂ ι q` whenever `p < q`, and a
**strong copy** if moreover `ι p ⊂ ι q` holds *only* when `p < q`.  A family is
weak (strong) `P`-free if it contains no weak (strong) copy of `P`.
`La(n, P)` (`La*(n, P)`) is the maximum size of a weak (strong) `P`-free family
in `2^[n]`.

The poset `B_d` is the Boolean lattice on `d` atoms, formalized here as
`Finset (Fin d)` with the inclusion order (`BoolLat d`).

## Main results

* `layers_weakFree` — any `d` consecutive layers of `2^[n]` are weak `B_d`-free;
  hence `e(B_d) ≥ d` and `La(n, B_d) ≥ ∑ᵢ C(n, i)` over `d` consecutive layers
  (`sum_choose_le_La`).
* `exists_strongCopy_layers` — any `d + 1` consecutive layers of `2^[n]`
  (with enough room, `a + d ≤ n`) contain a *strong* copy of `B_d`.
* `weakFree_layers_iff`, `strongFree_layers_iff` — combining the two: `k`
  consecutive layers are weak (strong) `B_d`-free **iff** `k ≤ d`.  This is the
  statement `e(B_d) = e*(B_d) = d`.
* `La_boolLatOne_eq` — **Sperner's theorem in this language**: `La(n, B_1)` is
  exactly `C(n, ⌊n/2⌋)`, i.e. for `d = 1` the layer construction is optimal and
  no `ε`-improvement is possible.  (The content of the paper is that for `d = 3`,
  in contrast, a positive `ε`-improvement does exist.)
* `La_mono_of_strictMono`, `La_boolLat_mono` — `La` is monotone along strictly
  monotone injections of posets, in particular `La(n, B_d) ≤ La(n, B_(d+1))`.
* `mul_choose_le_La`, `three_mul_choose_le_La_boolLat3` — quantitative forms of the
  layer bound, e.g. `3 · C(n, ⌊n/2⌋ - 2) ≤ La(n, B_3)`.
* `La_lt_two_pow`, `La_boolLat_eq_of_card_eq`, `La_boolLat3_fin3` — `La(n, B_d) < 2^n`
  for `d ≤ n`, with the exact values `La(d, B_d) = 2^d - 1` and `La(3, B_3) = 7`.
* `LaStar_boolLat_eq_of_card_eq`, `La_eq_LaStar_of_card_eq` — the same exact value for the
  strong extremal function, so `La(d, B_d) = La*(d, B_d) = 2^d - 1`.

Maximality of the layer construction, the exact value `La(d+1, B_d) = 2^(d+1) - 2`, and the
general upper bound `La(n, B_d) ≤ (2^d - 1)·C(n, ⌊n/2⌋)` are proved in
`Catalog/Bridges/B3FreeFamiliesBounds.lean`.
-/


open B3Free

open Finset

/-! ## Weak and strong copies -/

variable {α : Type*}









/-! ## Layers of the Boolean lattice -/

variable [DecidableEq α] [Fintype α]





/-! ## The Boolean lattice poset `B_d` -/




/-! ## Strong copies inside `d + 1` layers -/


variable {d : ℕ} (s : Finset α) (f : Fin d → α)









/-! ## The extremal functions `La` and `La*` -/

theorem B3Free.sum_choose_le_La(a d : ℕ) :
    ∑ i ∈ Finset.Ico a (a + d), (Fintype.card α).choose i ≤ La α (BoolLat d) := by sorry
