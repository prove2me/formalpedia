-- Prove2me | Definitions.Def_Geometry_SchubertCalculus_Flags
-- name    : Geometry_SchubertCalculus_Flags
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:23.111653+00:00
-- url     : https://prove2.me/theorems/90ded783-33e6-4b52-93c7-455b10ee0d5b
-- title:
--   Aether Catalog definitions — Geometry_SchubertCalculus_Flags
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SchubertCalculus.Flags`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SchubertCalculus/Flags.lean by skeleton subtraction
import Mathlib
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

namespace SchubertCalculus

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A complete flag of length `n`: an increasing chain of subspaces of dimensions
`0, 1, …, n` whose top member is the whole space. -/
structure CompleteFlag (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (n : ℕ) where
  /-- The `i`-th member of the flag. -/
  part : ℕ → Submodule K V
  /-- The chain is increasing. -/
  mono : Monotone part
  /-- `part i` has dimension `i` for `i ≤ n`. -/
  finrank_part : ∀ i ≤ n, finrank K (part i) = i
  /-- The flag exhausts the space. -/
  part_top : part n = ⊤

namespace CompleteFlag

variable {n : ℕ} (Fl : CompleteFlag K V n)


section

variable [FiniteDimensional K V] (W : Submodule K V)



/-- The *jump set* of `W` relative to the flag: the set of indices at which
`dim (W ⊓ F_•)` increases. -/
noncomputable def jumpSet (W : Submodule K V) : Finset ℕ :=
  (Finset.range n).filter fun i =>
    finrank K ((W ⊓ Fl.part (i + 1) : Submodule K V)) =
      finrank K ((W ⊓ Fl.part i : Submodule K V)) + 1






end

section Cells

variable [FiniteDimensional K V]

/-- The Schubert cell of the flag associated with a set `S` of jump positions: the set of
subspaces whose jump set is exactly `S`. -/
def cell (S : Finset ℕ) : Set (Submodule K V) := {W | Fl.jumpSet W = S}




end Cells

end CompleteFlag

end SchubertCalculus


