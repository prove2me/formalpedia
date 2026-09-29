-- Prove2me | Theorems.Thm_GreedyIndependentSet_turan_bound_of_cliqueFree
-- name    : GreedyIndependentSet.turan_bound_of_cliqueFree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:48:31.960049+00:00
-- url     : https://prove2.me/theorems/869154c5-89f4-44bb-b1e6-eeff8a2feb11
-- title:
--   Turán's theorem via Caro–Wei.
-- statement:
--   **Turán's theorem via Caro–Wei.**  A `K_{r+1}`-free graph on an arbitrary finite vertex type
--   has at most `(1 - 1/r)·n²/2` edges.  No divisibility hypothesis is needed: the bound comes from
--   applying the greedy Caro–Wei bound to the complement graph and then Sedrakyan's form of the
--   Cauchy–Schwarz inequality.
--
--   ```lean
--   theorem GreedyIndependentSet.turan_bound_of_cliqueFree{r : ℕ} (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
--       (#G.edgeFinset : ℝ) ≤ (1 - 1 / r) * (Fintype.card V) ^ 2 / 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CaroWeiGreedy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CaroWeiGreedy.lean#L193

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

theorem GreedyIndependentSet.turan_bound_of_cliqueFree{r : ℕ} (hr : 1 ≤ r) (h : G.CliqueFree (r + 1)) :
    (#G.edgeFinset : ℝ) ≤ (1 - 1 / r) * (Fintype.card V) ^ 2 / 2 := by sorry
