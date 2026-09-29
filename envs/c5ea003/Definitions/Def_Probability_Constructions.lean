-- Prove2me | Definitions.Def_Probability_Constructions
-- name    : Probability_Constructions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:30.42242+00:00
-- url     : https://prove2.me/theorems/53f0f06f-f30a-475a-9065-f07e186b3ddc
-- title:
--   Aether Catalog definitions — Probability_Constructions
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Constructions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Constructions.lean by skeleton subtraction
import Mathlib
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

namespace PackingIsolation

/-! ## Complete graphs -/



/-! ## Path graphs -/

/-- The path graph on `Fin n`: vertices `i` and `j` are adjacent iff their values are
consecutive naturals. -/
def PathG (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := by intro i j h; tauto
  loopless := ⟨by intro _ h; omega⟩

instance (n : ℕ) : DecidableRel (PathG n).Adj :=
  fun i j => inferInstanceAs (Decidable (i.val + 1 = j.val ∨ j.val + 1 = i.val))



/-- The candidate packing-isolating set for `P_n`: indices congruent to `1` mod `3`. -/
def pathPacking (n : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val % 3 = 1)








end PackingIsolation


