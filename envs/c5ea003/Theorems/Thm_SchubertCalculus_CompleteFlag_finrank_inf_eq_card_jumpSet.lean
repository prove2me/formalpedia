-- Prove2me | Theorems.Thm_SchubertCalculus_CompleteFlag_finrank_inf_eq_card_jumpSet
-- name    : SchubertCalculus.CompleteFlag.finrank_inf_eq_card_jumpSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:50:08.097824+00:00
-- url     : https://prove2.me/theorems/d8536805-b2de-4a25-a394-cbf05f43f47c
-- title:
--   Schubert dimension datum.
-- statement:
--   **Schubert dimension datum.** For every `j ≤ n`, the dimension of `W ⊓ F_j` equals the
--   number of jumps of `W` strictly below `j`.
--
--   ```lean
--   theorem SchubertCalculus.CompleteFlag.finrank_inf_eq_card_jumpSet{j : ℕ} (hj : j ≤ n) :
--       finrank K ((W ⊓ Fl.part j : Submodule K V)) =
--         ((Fl.jumpSet W).filter fun i => i < j).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/SchubertCalculus/Flags.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/SchubertCalculus/Flags.lean#L120

-- Thm stub generated from Geometry/SchubertCalculus/Flags.lean
import Mathlib
import Definitions.Def_Geometry_SchubertCalculus_Flags
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Schubert calculus I: complete flags, jump sequences and the cell decomposition

This file provides rigorous foundations for the combinatorial skeleton of the Grassmannian
that underlies Schubert's enumerative calculus.

Given a complete flag `0 = F₀ ⊂ F₁ ⊂ ⋯ ⊂ Fₙ = V` in an `n`-dimensional vector space and a
`k`-dimensional subspace `W ≤ V`, the *jump set*
`J(W) = {i < n | dim (W ⊓ Fᵢ₊₁) = dim (W ⊓ Fᵢ) + 1}` is the fundamental discrete invariant.

Main results:

* `SchubertCalculus.CompleteFlag.finrank_inf_step_le` : the dimension of `W ⊓ Fᵢ` grows by at
  most one at each step (a rank–nullity argument through the one dimensional quotient
  `Fᵢ₊₁ / Fᵢ`);
* `SchubertCalculus.CompleteFlag.finrank_inf_eq_card_jumpSet` : `dim (W ⊓ F_j)` equals the
  number of jumps below `j` — the exact "Schubert dimension datum" of `W`;
* `SchubertCalculus.CompleteFlag.card_jumpSet` : the jump set has exactly `k = dim W` elements,
  so that jump sets are indexed by `k`-element subsets of `{0, …, n-1}`;
* `SchubertCalculus.CompleteFlag.cell_pairwise_disjoint` /
  `SchubertCalculus.CompleteFlag.mem_cell_jumpSet` : the Schubert cells partition the
  Grassmannian.

Everything is stated for an arbitrary field and an arbitrary complete flag.
-/

open SchubertCalculus

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]


open CompleteFlag

variable {n : ℕ} (Fl : CompleteFlag K V n)



variable [FiniteDimensional K V] (W : Submodule K V)

theorem SchubertCalculus.CompleteFlag.finrank_inf_eq_card_jumpSet{j : ℕ} (hj : j ≤ n) :
    finrank K ((W ⊓ Fl.part j : Submodule K V)) =
      ((Fl.jumpSet W).filter fun i => i < j).card := by sorry
