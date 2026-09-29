-- Prove2me | Theorems.Thm_Hashimoto_exists_walk_of_dartChain
-- name    : Hashimoto.exists_walk_of_dartChain
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:46:34.463483+00:00
-- url     : https://prove2.me/theorems/2352276b-7cd3-4be7-a19a-baa6d8cc8e87
-- title:
--   Darts to walks.
-- statement:
--   **Darts to walks.** A list of darts in which consecutive darts are composable is the
--   dart list of a walk between the prescribed endpoints. This inverts
--   `SimpleGraph.Walk.darts`.
--
--   ```lean
--   theorem Hashimoto.exists_walk_of_dartChain:
--       ∀ (c : List G.Dart) (a b : V),
--         List.IsChain (fun d d' : G.Dart => d.toProd.2 = d'.toProd.1) c →
--         (∀ d ∈ c.head?, d.toProd.1 = a) →
--         (∀ d ∈ c.getLast?, d.toProd.2 = b) →
--         (c = [] → a = b) →
--         ∃ p : G.Walk a b, p.darts = c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/AcyclicVanishing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/AcyclicVanishing.lean#L39

-- Thm stub generated from Algebra/NonBacktracking/AcyclicVanishing.lean
import Mathlib

/-!
# Forests have identically vanishing non-backtracking trace

`Algebra.NonBacktracking.CyclePositivity` shows that a cycle in `G` forces some positive
power of the Hashimoto matrix to have positive trace. Here we prove the converse
implication, completing the characterisation

`G.IsAcyclic ↔ ∀ n ≥ 1, trace (B ^ n) = 0`.

The mathematical content is that a *closed* non-backtracking walk cannot exist in a
forest. The proof turns a cyclic list of darts into an honest `SimpleGraph.Walk`; the
non-backtracking condition says exactly that consecutive edges of that walk differ, and
in an acyclic graph such a walk is a path (`SimpleGraph.IsAcyclic.isPath_iff_isChain`).
A closed path is trivial, so the walk has length `0`, contradicting `n ≥ 1`.

## Main results

* `Hashimoto.exists_walk_of_dartChain` — a composable list of darts is the dart list of a
  walk (the inverse construction to `SimpleGraph.Walk.darts`);
* `Hashimoto.isChain_ne_edges_of_isChain_nbAdj` — non-backtracking dart chains have
  chains of pairwise-consecutively-distinct edges;
* `Hashimoto.trace_hashimoto_pow_eq_zero_of_isAcyclic` — forests kill all positive
  powers of `B`;
* `Hashimoto.isAcyclic_iff_trace_hashimoto_pow_eq_zero` — the resulting characterisation;
* `Hashimoto.closedNBWalks_eq_empty_of_isAcyclic` — the combinatorial form: a forest has
  no rooted closed non-backtracking walk of positive length.
-/

open Finset SimpleGraph List


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Reconstructing a walk from its darts -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in

theorem Hashimoto.exists_walk_of_dartChain:
    ∀ (c : List G.Dart) (a b : V),
      List.IsChain (fun d d' : G.Dart => d.toProd.2 = d'.toProd.1) c →
      (∀ d ∈ c.head?, d.toProd.1 = a) →
      (∀ d ∈ c.getLast?, d.toProd.2 = b) →
      (c = [] → a = b) →
      ∃ p : G.Walk a b, p.darts = c := by sorry
