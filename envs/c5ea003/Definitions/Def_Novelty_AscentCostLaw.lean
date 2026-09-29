-- Prove2me | Definitions.Def_Novelty_AscentCostLaw
-- name    : Novelty_AscentCostLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:03:24.491629+00:00
-- url     : https://prove2.me/theorems/1b11e803-bfe6-40e5-9689-1c73f7f2b6f2
-- title:
--   Aether Catalog definitions — Novelty_AscentCostLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AscentCostLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AscentCostLaw.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Ascent-cost laws: exact economics of a branch oracle under end-verification semantics

A search agent must climb a ternary decision tree of height `h`.  At every level it consults a
*branch oracle* which names the correct child with probability `α`.  Verification happens only at
the leaf (end-verification-only semantics): a wrong turn is discovered only after the whole wrong
subtree has been exhausted.  Two schedules are priced exactly here.

* **DFS with backtracking.**  Entering level `j` costs one visit; with the level failure weight
  `K = (1 - α)(2 - α)` the agent additionally burns a complete wrong ternary subtree of
  `(3 ^ j - 1) / 2` nodes.  Summing the levels gives the closed law
  `E_dfs(h) = h (1 - K/2) + K (3 ^ (h+1) - 3) / 4` (`dfsCost_eq_dfsCostRec`).
* **Restart from root.**  A full descent succeeds with probability `α ^ h`; failures are detected
  only at the leaf, so each attempt costs `h` visits and the number of attempts is geometric.  Its
  mean is exactly `E_restart(h) = h α ^ (-h)` (`restartCost_eq_expected_work`).

The formal findings, each a theorem below.

* **Effective branching is refuted.**  For *every* `α < 1` the DFS law has growth ratio exactly
  `3` in the limit (`dfs_growth_ratio_tendsto_three`); oracle accuracy enters only through the
  prefactor `3K/4` (`dfsCost_div_pow_tendsto`).  There is no "effective branching factor" below
  `3`.
* **The α = 1/3 dominance boundary.**  Restart beats DFS by an unbounded factor exactly when
  `α > 1/3` (`restart_dominates_dfs`), and loses by an unbounded factor when `α < 1/3`
  (`dfs_dominates_restart`).  This is the exact form of the empirical "restart dominates in 99%
  of cells".
* **Beam (exhaustive level sweep) never wins** — `dfsCost_le_beamCost`, for every `α ∈ [0,1]`.
* **The master hint law is refuted.**  The class-hint law of the earlier ledger saturates at a
  cap `1/θ = 3`; the branch-hint speedup `(3α) ^ h` is unbounded for every `α > 1/3`
  (`hintSpeedup_unbounded`), so no constant cap can hold.  Sequential hints compound
  geometrically (`restartCost_add`, `successProb_add`).
* **Exponential → polynomial phase transition at α = 1**: `restartCost 1 h = h` while for `α < 1`
  the cost per unit depth diverges (`restartCost_div_depth_atTop`).
* **Breakeven against a fixed exact-solver budget** is a genuine threshold: cost is strictly
  decreasing in `α` (`restartCost_strictAnti`), and an explicit critical accuracy
  `α* = ((1+c) h / F) ^ (1/h)` separates win from loss (`breakeven_threshold`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): oracle accuracy buys a smaller *base*, i.e. an effective branching
factor `b(α) < 3`, so that a modest `α` already converts exponential ascent into a cheap climb.

Experiment (Experimenter): the closed law was evaluated numerically (see
`ComputationalEvidence.md`).  With `K = (1-α)(2-α)`: at `α = 0.9`, `K = 0.11`,
`E_dfs(10) = 10·0.945 + 0.11·(3^11-3)/4 = 4880.91`, while the predicted leading term
`3^10 · 3K/4 = 4871.54` — the ratio `E(h+1)/E(h)` is `2.99636` at `h = 10` and `2.99994` at
`h = 14`, i.e. pinned at `3`.  At `α = 0.99` the same ratio is `2.99434` at `h = 12`.  Restart:
`E_restart(10) = 10·0.9^{-10} = 28.68`, more than two orders below DFS; at `α = 0.3 < 1/3`,
`E_restart(10) = 1.69·10^6` against `E_dfs(10) = 5.27·10^4`, so DFS wins — the boundary is at
`3α = 1` exactly, as the two dominance theorems below assert.

Analysis (Analyst): the DFS law is a geometric sum whose top term `K 3^{h+1}/4` dwarfs the linear
term; accuracy scales that prefactor to `0` continuously as `α → 1` but never touches the base.
The restart law is the one that changes base, from `3` to `1/α`, which is why the crossover sits
at `α = 1/3` and why the empirical speedup diverges instead of saturating at the class-hint cap.

Critique (Critic): `restartCost` is only meaningful for `α > 0`, so every comparison theorem
carries `0 < α`; `dfsCost` bounds require `α ∈ [0,1]` to keep `K ∈ [0,2]` and `1 - K/2 ≥ 0`,
which is stated as `failWeight_nonneg` / `failWeight_le_two` rather than assumed silently.  The
`α = 1` case of the geometric expectation is degenerate (`1 - α ^ h = 0`) and is proved
separately inside `tsum_geometric_trials`.
-/

namespace AscentCostLaw

open Filter Topology

/-! ### The two cost laws -/

/-- Level failure weight `K = (1 - α)(2 - α)` of a ternary branch oracle of accuracy `α`:
the expected number of *wrong* children fully expanded before the right one is taken, doubled;
equivalently `K/2 = (1-α)(2-α)/2` is the mean count of wasted siblings. -/
noncomputable def failWeight (α : ℝ) : ℝ := (1 - α) * (2 - α)

/-- Cost of the `j`-th level of a DFS ascent: one visit, plus (weighted by `K`) a complete wrong
ternary subtree of `(3 ^ j - 1)/2` nodes, which end-verification forces the agent to exhaust. -/
noncomputable def dfsLevelCost (α : ℝ) (j : ℕ) : ℝ := 1 + failWeight α * ((3 : ℝ) ^ j - 1) / 2

/-- The DFS ascent cost, defined by accumulating level costs. -/
noncomputable def dfsCostRec (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | h + 1 => dfsCostRec α h + dfsLevelCost α (h + 1)

/-- The closed-form DFS ascent law `E = h (1 - K/2) + K (3 ^ (h+1) - 3)/4`. -/
noncomputable def dfsCost (α : ℝ) (h : ℕ) : ℝ :=
  h * (1 - failWeight α / 2) + failWeight α * ((3 : ℝ) ^ (h + 1) - 3) / 4

/-- Probability that a full depth-`h` descent guided by an accuracy-`α` oracle is correct. -/
noncomputable def successProb (α : ℝ) (h : ℕ) : ℝ := α ^ h

/-- The restart-from-root ascent law `E = h α ^ (-h)`. -/
noncomputable def restartCost (α : ℝ) (h : ℕ) : ℝ := (h : ℝ) / α ^ h

/-- Exhaustive level sweep (beam of full width `3`): all `(3 ^ (h+1) - 3)/2` internal nodes. -/
noncomputable def beamCost (h : ℕ) : ℝ := ((3 : ℝ) ^ (h + 1) - 3) / 2

/-! ### Elementary properties of the failure weight -/




/-! ### Law 1: the exact DFS backtracking cost -/


/-! ### Law 2: the exact restart-from-root cost -/





/-! ### Effective branching is refuted: the base stays pinned at 3 -/



/-! ### The α = 1/3 dominance boundary -/






/-! ### Beam never wins -/



/-! ### Boundary calibration of the DFS law -/



/-! ### The master hint law is refuted -/

/-- Speedup of an accuracy-`α` branch oracle over the uninformed ternary baseline `α = 1/3`,
measured with the restart law. -/
noncomputable def hintSpeedup (α : ℝ) (h : ℕ) : ℝ := restartCost (1/3) h / restartCost α h




/-! ### Exponential → polynomial phase transition at α = 1 -/



/-! ### Breakeven against a fixed exact-solver budget -/



end AscentCostLaw


