-- Prove2me | Definitions.Def_Novelty_AscentCostBranching
-- name    : Novelty_AscentCostBranching
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:04:38.797692+00:00
-- url     : https://prove2.me/theorems/f8afc922-eef7-4fcd-87d5-41595c701e98
-- title:
--   Aether Catalog definitions — Novelty_AscentCostBranching
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AscentCostBranching`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AscentCostBranching.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AscentCostExponent
import Definitions.Def_Novelty_AscentCostLaw
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Universality: the ascent economy at branching factor `b`

Cycles 1–2 priced the ternary ascent and found a phase boundary at accuracy `α = 1/3`.  This
third cycle removes the `3`.  For an arbitrary branching factor `b ≥ 2` and an arbitrary level
waste weight `w ∈ (0, b-1]` the DFS ascent law is

`E_b(h) = h (1 - w/(b-1)) + w (b^(h+1) - b) / (b-1)^2`,

which for `b = 3`, `w = (1-α)(2-α)` is exactly the law of cycle 1 (`dfsCostB_specializes`).

Main results.

* `dfsCostB_eq_rec` : the closed law is the accumulated per-level cost
  `1 + w (b^j - 1)/(b-1)` (one visit, plus a wasted complete subtree of `(b^j-1)/(b-1)` nodes).
* `dfsB_growth_ratio_tendsto` : **effective branching is refuted at every branching factor** —
  the growth ratio is exactly `b`, for every waste weight `w > 0`.
* `restart_dominates_dfsB` / `dfsB_dominates_restart` : **the crossover is exactly at the
  reciprocal branching factor** `α = 1/b`.  Above it, restart-from-root wins by an unbounded
  factor; below it, DFS wins by an unbounded factor.  The `1/3` of cycle 1 was `1/b`.
* `ascent_exponent_law_general` : the optimal exponent is `min (b, 1/α)`, a nonsmooth function of
  accuracy with its kink at `α = 1/b`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 3): the `1/3` boundary is not about ternary trees; it is the
reciprocal of whatever branching factor the search graph has, and the waste weight only moves the
prefactor.  Bold form: no schedule mixing the two ever produces a base strictly between `1/α` and
`b`.

Experiment (Experimenter): with `b = 5`, `w = b - 1 = 4` (blind agent) the law gives
`E_5(6) = 4·(5^7 - 5)/16 = 19530`, exactly the number of internal nodes of a depth-6 5-ary tree,
and `E_5(7)/E_5(6) = 5.00026`; with `w = 0.2` the same ratio is `4.97801` — the base is `5`
either way, the prefactor differs by a factor of `20`.  Restart at `b = 5`: the crossover
accuracy is `0.2`; at `α = 0.15 < 1/5`, `E_restart(8) = 8/0.15^8 = 3.12·10^7` against
`E_5(8) = 1.22·10^5` at `w = 1`, so DFS wins, while at `α = 0.25 > 1/5`, `E_restart(8) =
5.24·10^5` and restart pulls ahead as `h` grows (the ratio falls like `(1/(5·0.25))^h`).

Analysis (Analyst): the argument only uses that the wasted subtree at level `j` has
`Θ(b^j)` nodes and that a restart attempt costs `h` with success probability `α^h`.  Hence the
exponent law `min(b, 1/α)` is a statement about *any* end-verification search with geometric
subtree growth; the ternary case of cycles 1–2 is one point of a one-parameter family.

Critique (Critic): the waste weight must satisfy `w ≤ b - 1` (a level cannot waste more than its
wrong siblings) — otherwise the linear term turns negative and the "cost" can dip below zero at
small `h`, which is not a search cost.  `b ≥ 2` is needed for `b^h ≥ 2` at `h ≥ 1`, used in the
lower bound; a "branching factor" below `2` is not a branching factor.
-/

namespace AscentCostLaw

open Filter Topology

/-! ### The general law -/

/-- Cost of level `j` for branching factor `b` and level waste weight `w`. -/
noncomputable def dfsLevelCostB (b w : ℝ) (j : ℕ) : ℝ := 1 + w * (b ^ j - 1) / (b - 1)

/-- Accumulated general DFS cost. -/
noncomputable def dfsCostBRec (b w : ℝ) : ℕ → ℝ
  | 0 => 0
  | h + 1 => dfsCostBRec b w h + dfsLevelCostB b w (h + 1)

/-- Closed form of the general DFS ascent law. -/
noncomputable def dfsCostB (b w : ℝ) (h : ℕ) : ℝ :=
  h * (1 - w / (b - 1)) + w * (b ^ (h + 1) - b) / (b - 1) ^ 2



/-! ### Asymptotics of the general law -/



/-! ### Two-sided bounds -/



/-! ### The crossover sits at the reciprocal branching factor -/



/-! ### The general exponent law -/


/-- The optimal general schedule. -/
noncomputable def minCostB (b w α : ℝ) (h : ℕ) : ℝ := min (dfsCostB b w h) (restartCost α h)



end AscentCostLaw


