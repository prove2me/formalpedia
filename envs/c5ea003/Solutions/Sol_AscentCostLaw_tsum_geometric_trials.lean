-- Prove2me | solution 1 for AscentCostLaw.tsum_geometric_trials
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:46:11.411475+00:00
-- url     : https://prove2.me/submissions/d0615667-2538-46c5-80c8-334e4fdba23c

-- Sol generated from Novelty/AscentCostLaw.lean
import Mathlib
import Definitions.Def_Novelty_AscentCostLaw
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

open AscentCostLaw

open Filter Topology

/-! ### The two cost laws -/








/-! ### Elementary properties of the failure weight -/




/-! ### Law 1: the exact DFS backtracking cost -/


/-! ### Law 2: the exact restart-from-root cost -/





/-! ### Effective branching is refuted: the base stays pinned at 3 -/



/-! ### The α = 1/3 dominance boundary -/






/-! ### Beam never wins -/



/-! ### Boundary calibration of the DFS law -/



/-! ### The master hint law is refuted -/





/-! ### Exponential → polynomial phase transition at α = 1 -/



/-! ### Breakeven against a fixed exact-solver budget -/




open AscentCostLaw in
theorem solution{p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * (p * (1 - p) ^ n) = 1 / p := by
  rcases eq_or_lt_of_le hp1 with rfl | hlt
  · have hz : ∀ n : ℕ, n ≠ 0 → ((n : ℝ) + 1) * (1 * (1 - 1) ^ n) = 0 := by
      intro n hn
      rw [sub_self, zero_pow hn]
      ring
    rw [tsum_eq_single 0 hz]
    norm_num
  · set r : ℝ := 1 - p with hr
    have hr0 : 0 ≤ r := by simp [hr]; linarith
    have hr1 : r < 1 := by simp [hr]; linarith
    have h1 : HasSum (fun n : ℕ => (n : ℝ) * r ^ n) (r / (1 - r) ^ 2) := by
      apply hasSum_coe_mul_geometric_of_norm_lt_one
      rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
    have h2 : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr1
    have h3 := (h1.add h2).mul_left p
    have h4 : (fun n : ℕ => p * ((n : ℝ) * r ^ n + r ^ n))
        = fun n : ℕ => ((n : ℝ) + 1) * (p * (1 - p) ^ n) := by
      funext n; rw [← hr]; ring
    rw [h4] at h3
    rw [h3.tsum_eq]
    have hrp : 1 - r = p := by simp [hr]
    rw [hrp]
    field_simp
    ring
