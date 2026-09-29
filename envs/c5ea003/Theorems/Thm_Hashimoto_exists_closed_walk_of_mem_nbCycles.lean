-- Prove2me | Theorems.Thm_Hashimoto_exists_closed_walk_of_mem_nbCycles
-- name    : Hashimoto.exists_closed_walk_of_mem_nbCycles
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:35:46.343565+00:00
-- url     : https://prove2.me/theorems/f907a7f5-8815-4cd8-b134-3b450d2a9462
-- title:
--   From cyclic dart words to closed walks.
-- statement:
--   **From cyclic dart words to closed walks.** A cyclically non-backtracking word of `n`
--   darts is the dart list of a closed walk of length `n` whose consecutive edges differ.
--
--   ```lean
--   theorem Hashimoto.exists_closed_walk_of_mem_nbCycles{n : ℕ} (hn : 1 ≤ n) {c : List G.Dart}
--       (hc : c ∈ nbCycles G n) :
--       ∃ (v : V) (p : G.Walk v v), p.length = n ∧ List.IsChain (· ≠ ·) p.edges := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/NonBacktracking/AcyclicVanishing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/NonBacktracking/AcyclicVanishing.lean#L105

-- Thm stub generated from Algebra/NonBacktracking/AcyclicVanishing.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace

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

open Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Reconstructing a walk from its darts -/


/-! ## Non-backtracking means consecutive edges differ -/



/-! ## Vanishing of the trace on forests -/

theorem Hashimoto.exists_closed_walk_of_mem_nbCycles{n : ℕ} (hn : 1 ≤ n) {c : List G.Dart}
    (hc : c ∈ nbCycles G n) :
    ∃ (v : V) (p : G.Walk v v), p.length = n ∧ List.IsChain (· ≠ ·) p.edges := by sorry
