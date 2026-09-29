-- Prove2me | Theorems.Thm_CliqueComplexFlag_isClique_pair
-- name    : CliqueComplexFlag.isClique_pair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:08:51.38818+00:00
-- url     : https://prove2.me/theorems/c3b78a89-f422-4a6e-b155-4d3c47b36d12
-- title:
--   A two-element set is a clique iff its endpoints are adjacent.
-- statement:
--   **A two-element set is a clique iff its endpoints are adjacent.**
--   This is the structural pivot of the whole development.
--
--   ```lean
--   theorem CliqueComplexFlag.isClique_pair{G : SimpleGraph V} {u v : V} (h : u ≠ v) :
--       G.IsClique (↑({u, v} : Finset V) : Set V) ↔ G.Adj u v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RamseyTheory/CliqueComplexFlag.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RamseyTheory/CliqueComplexFlag.lean#L70

-- Thm stub generated from Geometry/RamseyTheory/CliqueComplexFlag.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
/-
# Clique Complexes, Flag Complexes, and the Vietoris–Rips Filtration

This file develops, from scratch, a lightweight theory of abstract simplicial
complexes (`ASC`) and the clique-complex construction on simple graphs, together
with the flag-complex characterization, the Vietoris–Rips filtration, and a
Turán-style bound on the `f`-vector.

## Main results

* `isClique_pair`            — a two-element set is a clique iff its endpoints are adjacent.
* `cliqueComplex_isFlag`     — every clique complex is a flag complex.
* `oneSkeleton_cliqueComplex`— the one-skeleton of `Δ(G)` is exactly `G`.
* `flag_eq_cliqueComplex`    — every flag complex *with all singletons* is the clique
                               complex of its own one-skeleton (the converse direction).
* `vietorisRips_mono`        — the Vietoris–Rips complex is monotone in the scale `ε`.
* `cliqueComplex_fVector_le_choose` — `f_k(Δ(G)) ≤ C(n, k+1)` (Turán-style upper bound).
* `flag_not_cliqueComplex_without_singletons` — the singleton hypothesis in
                               `flag_eq_cliqueComplex` cannot be dropped (counterexample).

-- !-- Lab Notebook -- !--
Hypothesis: the clique-complex and one-skeleton constructions form an
  adjunction-like pair on simple graphs, with flag complexes the image of `Δ`.
Result: proved both directions, with the precise side condition (all singletons
  present) isolated by an explicit counterexample on `Bool`.
Insight: the entire theory pivots on the single fact `isClique_pair`
  ("a 2-clique is an edge"); the forward direction is downward closure and the
  converse rebuilds a face from its edges via the flag axiom.
Failure analysis: the naive converse (drop the singleton hypothesis) is FALSE —
  clique complexes always contain every singleton, but a flag complex need not,
  witnessed by the trivial complex `{∅}` whose one-skeleton is the empty graph.
-- !-- Lab Notebook -- !--
-/

open CliqueComplexFlag

open scoped Classical

universe u
variable {V : Type u}


open ASC



/-! ## The clique complex of a simple graph -/

theorem CliqueComplexFlag.isClique_pair{G : SimpleGraph V} {u v : V} (h : u ≠ v) :
    G.IsClique (↑({u, v} : Finset V) : Set V) ↔ G.Adj u v := by sorry
