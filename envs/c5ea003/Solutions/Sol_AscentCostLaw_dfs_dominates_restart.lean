-- Prove2me | solution 1 for AscentCostLaw.dfs_dominates_restart
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:44:32.221114+00:00
-- url     : https://prove2.me/submissions/7b8072b6-18e1-4339-9ebd-9c6bae44abae

-- Sol generated from Novelty/AscentCostLaw.lean
import Mathlib
import Definitions.Def_Novelty_AscentCostLaw
import Theorems.Thm_AscentCostLaw_dfsCost_ge
import Theorems.Thm_AscentCostLaw_restartCost_pos
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

theorem failWeight_nonneg {α : ℝ} (h1 : α ≤ 1) : 0 ≤ failWeight α := by
  have : (0:ℝ) ≤ 1 - α := by linarith
  have : (0:ℝ) ≤ 2 - α := by linarith
  unfold failWeight; positivity


theorem failWeight_le_two {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : failWeight α ≤ 2 := by
  unfold failWeight; nlinarith

/-! ### Law 1: the exact DFS backtracking cost -/


/-! ### Law 2: the exact restart-from-root cost -/





/-! ### Effective branching is refuted: the base stays pinned at 3 -/



/-! ### The α = 1/3 dominance boundary -/


/-- Upper bound: the DFS law never exceeds depth plus a full level sweep. -/
theorem dfsCost_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) (h : ℕ) :
    dfsCost α h ≤ (h : ℝ) + (3 : ℝ) ^ (h + 1) / 2 := by
  have hK : 0 ≤ failWeight α := failWeight_nonneg h1
  have hK2 : failWeight α ≤ 2 := failWeight_le_two h0 h1
  have h3 : (0 : ℝ) < (3 : ℝ) ^ (h + 1) := by positivity
  have hh : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
  unfold dfsCost
  nlinarith [mul_nonneg hh hK]




/-! ### Beam never wins -/



/-! ### Boundary calibration of the DFS law -/



/-! ### The master hint law is refuted -/





/-! ### Exponential → polynomial phase transition at α = 1 -/



/-! ### Breakeven against a fixed exact-solver budget -/




open AscentCostLaw in
theorem solution{α : ℝ} (h0 : 0 < α) (hhigh : α < 1/3) :
    Filter.Tendsto (fun h : ℕ => dfsCost α h / restartCost α h) Filter.atTop (𝓝 0) := by
  have h1 : α < 1 := by linarith
  have hK : 0 ≤ failWeight α := failWeight_nonneg h1.le
  have hg : Filter.Tendsto (fun h : ℕ => α ^ h + (3 / 2) * (3 * α) ^ h) Filter.atTop (𝓝 0) := by
    have t1 : Filter.Tendsto (fun h : ℕ => α ^ h) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
    have t2 : Filter.Tendsto (fun h : ℕ => (3 * α) ^ h) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by linarith)
    simpa using t1.add (t2.const_mul (3 / 2 : ℝ))
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hd : 0 ≤ dfsCost α h := le_trans (by positivity) (dfsCost_ge h0.le h1.le hh)
    exact div_nonneg hd (restartCost_pos h0 hh).le
  · filter_upwards [eventually_ge_atTop 1] with h hh
    have hhr : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
    have hup : dfsCost α h ≤ (h : ℝ) + (3 : ℝ) ^ (h + 1) / 2 := dfsCost_le h0.le h1.le h
    have hr : 0 < restartCost α h := restartCost_pos h0 hh
    rw [div_le_iff₀ hr]
    have hRHS : (α ^ h + (3 / 2) * (3 * α) ^ h) * restartCost α h
        = (h : ℝ) + (3 / 2) * (h : ℝ) * 3 ^ h := by
      have hαh : (α : ℝ) ^ h ≠ 0 := (pow_pos h0 h).ne'
      unfold restartCost
      rw [mul_pow]
      field_simp
    rw [hRHS]
    have h3 : (0 : ℝ) < (3 : ℝ) ^ h := by positivity
    have hsucc : (3 : ℝ) ^ (h + 1) / 2 = (3 / 2) * 3 ^ h := by rw [pow_succ]; ring
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ (h : ℝ) - 1) h3.le]
