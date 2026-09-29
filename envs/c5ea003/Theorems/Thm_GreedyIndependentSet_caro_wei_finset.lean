-- Prove2me | Theorems.Thm_GreedyIndependentSet_caro_wei_finset
-- name    : GreedyIndependentSet.caro_wei_finset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:38.527583+00:00
-- url     : https://prove2.me/theorems/5a24ee0c-d55e-499c-a17d-c4c8cd22b5cc
-- title:
--   Caro–Wei, relative form.
-- statement:
--   **Caro–Wei, relative form.**  For every vertex subset `t` there is an independent set
--   `s ⊆ t` whose size is at least `∑_{v ∈ t} 1/(deg_t v + 1)`, where `deg_t` counts only
--   neighbours inside `t`.  The proof is the greedy algorithm: repeatedly pick a vertex of minimum
--   relative degree and delete its closed neighbourhood.
--
--   ```lean
--   theorem GreedyIndependentSet.caro_wei_finset(t : Finset V) :
--       ∃ s ⊆ t, G.IsIndepSet (s : Set V) ∧
--         ∑ v ∈ t, (1 : ℝ) / (degIn G t v + 1) ≤ #s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CaroWeiGreedy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CaroWeiGreedy.lean#L71

-- Thm stub generated from Bridges/CaroWeiGreedy.lean
import Mathlib
import Definitions.Def_Bridges_CaroWeiGreedy
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: the probabilistic Caro–Wei bound ↔ a greedy (constructive) independent set

The Caro–Wei inequality
`α(G) ≥ ∑_v 1 / (deg v + 1)`
is the textbook example of the *probabilistic method with alterations*: order the vertices
uniformly at random and keep the vertices that precede all of their neighbours; the expected
number of kept vertices is `∑_v 1/(deg v + 1)`.

This file proves the inequality **without any probability space at all**: the whole content is a
strong induction that repeatedly deletes the closed neighbourhood of a vertex of *minimum*
degree, i.e. the greedy algorithm.  This is the constructive shadow of the expectation argument,
in the exact spirit of the mission ("Erdős's existence proofs are algorithms in disguise").

Main results:

* `GreedyIndependentSet.caro_wei_finset` — the induction engine, relativised to an arbitrary
  vertex subset `t`: there is an independent `s ⊆ t` with `∑_{v ∈ t} 1/(deg_t v + 1) ≤ #s`.
* `GreedyIndependentSet.caro_wei` — `∑_v 1/(deg v + 1) ≤ α(G)`.
* `GreedyIndependentSet.card_div_maxDegree_succ_le_indepNum` — the Turán-type corollary
  `n / (Δ + 1) ≤ α(G)`.
* `GreedyIndependentSet.turan_bound_of_cliqueFree` — Turán's theorem
  `#edges ≤ (1 - 1/r) n² / 2` for `K_{r+1}`-free graphs, on an *arbitrary* finite vertex type
  and with **no divisibility hypothesis**, obtained by applying Caro–Wei to the complement and
  Sedrakyan's (Cauchy–Schwarz) inequality.

## Catalog connections
* `Bridges/TuranExplicitCount.lean` : the explicit Turán graph attains this bound.
* `Bridges/ErdosProbabilisticRamsey.lean`, `Bridges/LovaszLocalLemmaFinite.lean` : the other
  members of the probabilistic-method trio.
-/

open Finset SimpleGraph

open GreedyIndependentSet

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]







omit [Fintype V] in

theorem GreedyIndependentSet.caro_wei_finset(t : Finset V) :
    ∃ s ⊆ t, G.IsIndepSet (s : Set V) ∧
      ∑ v ∈ t, (1 : ℝ) / (degIn G t v + 1) ≤ #s := by sorry
