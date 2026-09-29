-- Prove2me | solution 1 for CliqueComplexFlag.cliqueComplex_isFlag
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:39.478998+00:00
-- url     : https://prove2.me/submissions/1b2d0c83-649c-41a0-af2f-e4c422ea4f13

-- Sol generated from Geometry/RamseyTheory/CliqueComplexFlag.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
import Theorems.Thm_CliqueComplexFlag_isClique_pair
import Theorems.Thm_CliqueComplexFlag_mem_cliqueComplex
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




/-! ## The one-skeleton of a complex -/




/-! ## Flag complexes -/




/-! ## The Vietoris–Rips complex -/




/-! ## The f-vector and a Turán-style bound -/



/-! ## The singleton hypothesis is necessary -/




open CliqueComplexFlag in
theorem solution(G : SimpleGraph V) : IsFlag (cliqueComplex G) := by
  -- !-- a set all of whose pairs are edges is pairwise-adjacent, i.e. a clique. -- !--
  intro s _ hpairs
  rw [mem_cliqueComplex, SimpleGraph.isClique_iff]
  intro u hu v hv huv
  have : ({u, v} : Finset V) ∈ (cliqueComplex G).faces :=
    hpairs u (by exact_mod_cast hu) v (by exact_mod_cast hv) huv
  rw [mem_cliqueComplex] at this
  exact (isClique_pair huv).1 this
