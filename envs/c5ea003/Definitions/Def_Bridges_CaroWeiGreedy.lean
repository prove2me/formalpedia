-- Prove2me | Definitions.Def_Bridges_CaroWeiGreedy
-- name    : Bridges_CaroWeiGreedy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:35.514422+00:00
-- url     : https://prove2.me/theorems/c4425ebd-55a8-4fa4-8920-ba89b405399b
-- title:
--   Aether Catalog definitions — Bridges_CaroWeiGreedy
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CaroWeiGreedy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CaroWeiGreedy.lean by skeleton subtraction
import Mathlib
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

namespace GreedyIndependentSet

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree of `v` measured inside the vertex subset `t`. -/
def degIn (t : Finset V) (v : V) : ℕ := #(t.filter fun w => G.Adj v w)



/-- The closed neighbourhood of `v` inside `t`. -/
private def closedNbhd (t : Finset V) (v : V) : Finset V := insert v (t.filter fun w => G.Adj v w)









/-! ## From greedy independence to the off-diagonal Ramsey bound `R(3, k+1) > k²`

A triangle-free graph has independent neighbourhoods, so `Δ ≤ α`; combined with the greedy bound
`n ≤ α(Δ+1)` this gives `n ≤ α(α+1)`.  Contrapositively, a graph on more than `k(k+1)` vertices
contains a triangle or an independent set of size `k+1` — a verified lower bound for the
off-diagonal Ramsey number `R(3, k+1)`, obtained with no probability at all. -/





/-! ## Lab notes: sharpness of the two bounds

Experimental data (all checked by `decide` below, on the four-vertex Turán graph
`turanGraph 4 2`, which is the 4-cycle):

| quantity                       | value | source                            |
|--------------------------------|-------|-----------------------------------|
| `#edges`                       | `4`   | `card_edges_turanGraph_four_two`  |
| Turán bound `(1-1/2)·4²/2`     | `4`   | `turan_bound_sharp_four_two`      |
| `maxDegree`                    | `2`   | `maxDegree_turanGraph_four_two`   |
| greedy bound `n/(Δ+1) = 4/3`   | `1.33`| `card_div_maxDegree_succ_le_indepNum` |
| true independence number       | `2`   | the two colour classes            |

So the Turán inequality proved above is *attained* (it is not merely an upper bound), while the
`n/(Δ+1)` corollary is strict here — the loss is exactly the convexity slack in
Cauchy–Schwarz. -/





end GreedyIndependentSet


