-- Prove2me | Theorems.Thm_PackingIsolation_pathPacking_cover
-- name    : PackingIsolation.pathPacking_cover
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:32.602992+00:00
-- url     : https://prove2.me/theorems/662902c9-a947-4a75-8e52-6734ecbdcba1
-- title:
--   Coverage of a single edge `{a, a+1}`: a residue-`1`-mod-`3` vertex lies within
-- statement:
--   Coverage of a single edge `{a, a+1}`: a residue-`1`-mod-`3` vertex lies within
--   distance one of one of the two endpoints.
--
--   ```lean
--   theorem PackingIsolation.pathPacking_cover(n : ℕ) (a b : Fin n) (h : a.val + 1 = b.val) :
--       a ∈ nbhdSet (PathG n) (pathPacking n) ∨ b ∈ nbhdSet (PathG n) (pathPacking n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Constructions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Constructions.lean#L121

-- Thm stub generated from Probability/Constructions.lean
import Mathlib
import Definitions.Def_Probability_Constructions
import Definitions.Def_Probability_Defs
/-
  Packing-Isolating Sets — Existence in Two Block-Graph Families

  A *block graph* is a graph in which every block (maximal 2-connected subgraph) is a
  clique.  The conjecture under study asserts that every finite block graph admits a
  packing-isolating set.  Here we verify the conjecture constructively for two
  fundamental families of block graphs:

  * **Complete graphs** `K_{n+1}` — a single block which is itself a clique;
  * **Path graphs** `P_n` — trees, hence block graphs whose blocks are all edges `K₂`.

  Main results:
  * `completeGraph_packingIsolating` / `completeGraph_exists_packingIsolating`:
        any single vertex isolates a complete graph and is trivially a 2-packing.
  * `pathG_twoPacking`, `pathG_isolating`, `pathG_packingIsolating`,
        `pathG_exists_packingIsolating`:
        the residue class `{ i : i ≡ 1 (mod 3) }` is packing-isolating in `P_n` for
        every `n`.

  -- !-- Lab Notes -- !--
  Hypothesis (Stage 1, bold): a *single periodic pattern* of period 3 simultaneously
    realizes the 2-packing constraint (gaps ≥ 3) and the isolating constraint (every
    length-1 edge is covered) on an arbitrarily long path.
  Experiment (Stage 2): the candidate `S = {i | i % 3 = 1}`.  Disjointness reduces to
    "two residues equal to 1 mod 3 that differ are ≥ 3 apart" (pure `omega`); coverage
    of an edge `{i, i+1}` reduces to a 3-way case split on `i % 3`, where the witness
    in the residue-2 case must reach *backwards* to `i-1` to stay inside `[0,n)`.
  Analysis (Stage 3): the backward witness is the crucial subtlety — a naive forward
    pattern fails at the right endpoint, explaining why a maximal 2-packing need NOT be
    isolating (e.g. taking both endpoints of `P₆`); existence requires the *aligned*
    periodic set, not a greedy/maximal one.
  Critique (Stage 4): proofs use `omega`, `rcases`, explicit `Fin` witnesses — no
    `decide`/`simp`-only shortcut; the result is an infinite family, not a finite check.
  Synthesis (Stage 5): complete graphs (single clique block) and paths (chains of `K₂`
    blocks) bracket the structural spectrum of block graphs, giving real evidence for
    the general conjecture (left as a future direction).
-/

open Finset SimpleGraph

open PackingIsolation

/-! ## Complete graphs -/



/-! ## Path graphs -/

theorem PackingIsolation.pathPacking_cover(n : ℕ) (a b : Fin n) (h : a.val + 1 = b.val) :
    a ∈ nbhdSet (PathG n) (pathPacking n) ∨ b ∈ nbhdSet (PathG n) (pathPacking n) := by sorry
