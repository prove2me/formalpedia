-- Prove2me | Definitions.Def_Bridges_DenseSumsetFree_Basic
-- name    : Bridges_DenseSumsetFree_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:31.972955+00:00
-- url     : https://prove2.me/theorems/9e11b574-714c-4a89-869f-dc4dbecfcd3a
-- title:
--   Aether Catalog definitions — Bridges_DenseSumsetFree_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.DenseSumsetFree.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/DenseSumsetFree/Basic.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dense sets without large sumsets: basic notions

Fix `n` and consider the interval `[n] = {0, 1, …, n-1}`.  We are interested in
subsets `S ⊆ [n]` which are *dense* (`|S| ≥ δ n`) but which nevertheless contain
no sumset `A + B` with both summands large.

This file sets up the vocabulary:

* `AvoidsSumsets S k` — no sumset `A + B` with `|A|, |B| ≥ k` is contained in `S`;
* `subset_range_of_add_subset_range` — if `A + B ⊆ [n]` and `B ≠ ∅` then `A ⊆ [n]`
  (this is special to `ℕ`, where all elements are nonnegative);
* `card_add_ge` — the Cauchy–Davenport lower bound `|A| + |B| - 1 ≤ |A + B|`
  transported from `ℤ` to `ℕ`;
* `avoidsSumsets_of_card_lt` — the *baseline* (deterministic, linear) avoidance
  result: a set of size `< 2k - 1` avoids all `k`-sumsets;
* `DistinctSums A B` and `card_add_of_distinctSums` — the opposite extreme, where
  the `|A| · |B|` sums are pairwise different, so that `|A + B| = |A| · |B|`.

The main theorem of the development (in `Main.lean`) upgrades the baseline linear
threshold `k ≈ n/2` all the way down to a **polylogarithmic** threshold
`k = O((log n)^3)`, for sets of any fixed density `δ < 1`.
-/

open Finset Pointwise

namespace DenseSumsetFree

/-- `S` avoids `k`-sumsets: no sumset `A + B` with both `|A| ≥ k` and `|B| ≥ k`
is contained in `S`. -/
def AvoidsSumsets (S : Finset ℕ) (k : ℕ) : Prop :=
  ∀ A B : Finset ℕ, k ≤ A.card → k ≤ B.card → ¬ A + B ⊆ S







/-- `A` and `B` have *distinct sums* if the `|A| · |B|` sums `a + b` are pairwise
different. -/
def DistinctSums (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B, a₁ + b₁ = a₂ + b₂ → a₁ = a₂ ∧ b₁ = b₂



end DenseSumsetFree


