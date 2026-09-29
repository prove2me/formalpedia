-- Prove2me | Definitions.Def_Bridges_TropicalWalkPerron
-- name    : Bridges_TropicalWalkPerron
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:01.085246+00:00
-- url     : https://prove2.me/theorems/cfc921ca-2ce0-4109-96e0-76c97b8636e3
-- title:
--   Aether Catalog definitions — Bridges_TropicalWalkPerron
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalWalkPerron`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalWalkPerron.lean by skeleton subtraction
import Mathlib

/-!
# Walks, cycle means and the max-plus (tropical) Perron–Frobenius eigenvector

This file develops, from scratch, the combinatorial machinery needed to prove the
existence of a max-plus eigenvector for an arbitrary finite real matrix:

  for every `A : V → V → ℝ` on a nonempty finite type `V` there are `μ : ℝ`
  and `v : V → ℝ` with `max_j (A i j + v j) = μ + v i` for all `i`.

Everything is finite: since all entries of `A` are real numbers (no `-∞`), the
underlying digraph is complete, so every pair of nodes is joined by walks of every
length.  The proof follows the Cuninghame-Green construction:

* `walkW A p m` is the weight of the first `m` edges of the walk `p : ℕ → V`;
* `bestW A m i j` is the maximal weight of a walk from `i` to `j` using `m + 1` edges;
* `cycleMax A` is the maximal cycle mean, taken over cycles of length at most `card V`;
* every closed walk has mean at most `cycleMax A` (`walkW_le_cycleMax`, proved by
  strong induction on the length using a pigeonhole splitting argument);
* after normalising `A` by `cycleMax A` one has a critical cycle of weight `0`, and
  the Kleene-star column `v i = max_{m ≤ 2·card V} bestW A m i c` is an eigenvector.

## Main results

* `walkW_le_cycleMax` : every closed walk has weight at most `length · cycleMax A`.
* `exists_normalized_eigenvector` : eigenvector existence for a normalised matrix.
* `exists_tropical_eigenvector` : the general tropical Perron–Frobenius statement.
-/

noncomputable section

open Finset

namespace TropicalWalk

variable {V : Type*}

/-! ### Walks and their weights -/

/-- Weight of the first `m` edges of the walk `p`. -/
def walkW (A : V → V → ℝ) (p : ℕ → V) (m : ℕ) : ℝ :=
  ∑ t ∈ Finset.range m, A (p t) (p (t + 1))



variable [Fintype V] [Nonempty V]

/-- Maximal weight of a walk from `i` to `j` using exactly `m + 1` edges. -/
def bestW (A : V → V → ℝ) : ℕ → V → V → ℝ
  | 0, i, j => A i j
  | (m + 1), i, j =>
      Finset.univ.sup' Finset.univ_nonempty (fun l => bestW A m i l + A l j)






/-! ### Prepending and concatenating -/



/-! ### Splitting a walk at a repeated vertex -/

/-- The walk obtained from `p` by deleting the loop between times `s` and `s + d`. -/
def cutWalk (p : ℕ → V) (s d : ℕ) : ℕ → V := fun u => if u ≤ s then p u else p (u + d)






/-! ### The maximal cycle mean -/

/-- Index set for cycles of length at most `card V`. -/
def cycleIndex (V : Type*) [Fintype V] : Finset (ℕ × V) :=
  (Finset.range (Fintype.card V)) ×ˢ (Finset.univ : Finset V)

lemma cycleIndex_nonempty : (cycleIndex V).Nonempty := by
  refine Finset.Nonempty.product ⟨0, Finset.mem_range.mpr Fintype.card_pos⟩ Finset.univ_nonempty

/-- The maximal cycle mean of `A`, taken over closed walks of at most `card V` edges. -/
def cycleMax (A : V → V → ℝ) : ℝ :=
  (cycleIndex V).sup' cycleIndex_nonempty
    (fun ki => bestW A ki.1 ki.2 ki.2 / (ki.1 + 1))



/-! ### Normalising by the maximal cycle mean -/



/-! ### The Kleene-star column and the eigenvector -/

lemma starRange_nonempty : (Finset.range (2 * Fintype.card V + 1)).Nonempty :=
  Finset.nonempty_range_iff.mpr (by omega)

/-- Kleene-star column at `c`: the best weight of a walk from `i` to `c` using at most
`2 · card V + 1` edges. -/
def starCol (A : V → V → ℝ) (c i : V) : ℝ :=
  (Finset.range (2 * Fintype.card V + 1)).sup' starRange_nonempty (fun m => bestW A m i c)



/-! ### General tropical Perron–Frobenius theorem -/


