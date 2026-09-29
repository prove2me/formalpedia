-- Prove2me | Theorems.Thm_SudokuSpectral_swapP_harmonic_iff
-- name    : SudokuSpectral.swapP_harmonic_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:08:44.161794+00:00
-- url     : https://prove2.me/theorems/fb30774f-6d62-4c0c-9705-af70259367f5
-- title:
--   A vector is fixed by the chain iff it satisfies the discrete mean-value
-- statement:
--   A vector is fixed by the chain **iff** it satisfies the discrete mean-value
--   property `deg(x) · f x = ∑_{y∼x} f y` at every vertex (given a nonzero move rate).
--   This is the algebraic characterization of harmonic functions of the walk.
--
--   ```lean
--   theorem SudokuSpectral.swapP_harmonic_iff(hc : c ≠ 0) (f : V → ℝ) :
--       (swapP G c).mulVec f = f ↔
--         ∀ x, (∑ y ∈ G.neighborFinset x, f y) = G.degree x * f x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SudokuSpectralGap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SudokuSpectralGap.lean#L128

-- Thm stub generated from Probability/SudokuSpectralGap.lean
import Mathlib
import Definitions.Def_Probability_SudokuSpectralGap
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Spectral Gap of a Constraint-Satisfaction Swap Chain

A *constraint-satisfaction puzzle* (of which Sudoku is the archetypal example) is
solved by a large collection of admissible completions.  A natural way to sample a
random completion is the **swap chain**: from a current completion, repeatedly pick
a *compatible swap* — a local move that exchanges two entries while preserving every
constraint — and follow it with some holding probability.  The mixing speed of this
chain is governed by its **spectral gap** `1 - λ₂`, the distance between the top
eigenvalue `1` and the second eigenvalue.

This file builds the swap chain from first principles as a symmetric, doubly
stochastic transition matrix attached to an arbitrary finite graph `G` of admissible
moves, and isolates the *exact* dictionary between the algebra of the chain and the
combinatorics of `G`:

* the chain is **stochastic** and **symmetric** (`swapP_row_sum`, `swapP_symm`),
  hence the uniform distribution is stationary and the constant vector is a
  top eigenvector (`swapP_mulVec_one`);
* a vector is fixed by the chain **iff** it satisfies a discrete mean-value
  property (`swapP_harmonic_iff`);
* **reducibility ⇒ vanishing gap**: if the move graph is disconnected, there is a
  *nonconstant* fixed vector, so the eigenvalue `1` is degenerate and the gap is
  `0` (`swapP_reducible_nonconstant_fixed`);
* **irreducibility ⇒ simple top eigenvalue**: if the move graph is connected, every
  fixed vector is constant — a discrete maximum principle
  (`swapP_fixed_const_of_preconnected`);
* an explicit two-state computation exhibits the second eigenvalue `1 - 2c` and the
  strictly positive gap `2c` in the connected case
  (`twoState_eigenvector`, `twoState_gap_pos`), versus the identically-degenerate
  gap of the disconnected case (`twoState_bot_eq_one`).

The upshot corrects a tempting but false folklore slogan.  The gap is **not** a
function of the number of clues or of the number of completions: two puzzles with
the same number of completions can have gap `2c > 0` or gap `0` depending only on
whether the graph of compatible swaps is connected.  Connectivity of the move graph,
not clue count, is the true order parameter.

A genuine Sudoku fixture (`sudoku_row_sum`) shows that a single compatible swap
inside a row preserves the row's value multiset, hence keeps the chain inside one
level set — the combinatorial reason the swap graph decomposes into invariant blocks.
-/

open scoped BigOperators
open Matrix

open SudokuSpectral

variable {V : Type*} [Fintype V] [DecidableEq V]


variable (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ)

theorem SudokuSpectral.swapP_harmonic_iff(hc : c ≠ 0) (f : V → ℝ) :
    (swapP G c).mulVec f = f ↔
      ∀ x, (∑ y ∈ G.neighborFinset x, f y) = G.degree x * f x := by sorry
