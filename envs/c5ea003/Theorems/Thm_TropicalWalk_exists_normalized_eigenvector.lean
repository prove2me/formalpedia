-- Prove2me | Theorems.Thm_TropicalWalk_exists_normalized_eigenvector
-- name    : TropicalWalk.exists_normalized_eigenvector
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:22:10.953409+00:00
-- url     : https://prove2.me/theorems/305bfd23-0afc-4826-80fe-d24f68b37071
-- title:
--   Eigenvector for a normalised matrix.
-- statement:
--   **Eigenvector for a normalised matrix.**  If no closed walk of `A` has positive
--   weight and some cycle through `c` has weight exactly `0`, then the Kleene-star column
--   at `c` is a max-plus eigenvector with eigenvalue `0`.
--
--   ```lean
--   theorem TropicalWalk.exists_normalized_eigenvector{A : V → V → ℝ}
--       (H1 : ∀ m : ℕ, 1 ≤ m → ∀ p : ℕ → V, p 0 = p m → walkW A p m ≤ 0)
--       {c : V} {L : ℕ} (hL : L < Fintype.card V) (hc : bestW A L c c = 0) :
--       ∃ v : V → ℝ, ∀ i : V,
--         Finset.univ.sup' Finset.univ_nonempty (fun j => A i j + v j) = v i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalWalkPerron.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalWalkPerron.lean#L385

-- Thm stub generated from Bridges/TropicalWalkPerron.lean
import Mathlib
import Definitions.Def_Bridges_TropicalWalkPerron

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

open TropicalWalk

variable {V : Type*}

/-! ### Walks and their weights -/




variable [Fintype V] [Nonempty V]







/-! ### Prepending and concatenating -/



/-! ### Splitting a walk at a repeated vertex -/







/-! ### The maximal cycle mean -/






/-! ### Normalising by the maximal cycle mean -/



/-! ### The Kleene-star column and the eigenvector -/

theorem TropicalWalk.exists_normalized_eigenvector{A : V → V → ℝ}
    (H1 : ∀ m : ℕ, 1 ≤ m → ∀ p : ℕ → V, p 0 = p m → walkW A p m ≤ 0)
    {c : V} {L : ℕ} (hL : L < Fintype.card V) (hc : bestW A L c c = 0) :
    ∃ v : V → ℝ, ∀ i : V,
      Finset.univ.sup' Finset.univ_nonempty (fun j => A i j + v j) = v i := by sorry
