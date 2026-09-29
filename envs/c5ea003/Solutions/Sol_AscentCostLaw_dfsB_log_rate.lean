-- Prove2me | solution 1 for AscentCostLaw.dfsB_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:37:36.955356+00:00
-- url     : https://prove2.me/submissions/78fe0abe-b0b3-4c20-a1c5-57bba03d88fd

-- Sol generated from Novelty/AscentCostBranching.lean
import Mathlib
import Definitions.Def_Novelty_AscentCostBranching
import Definitions.Def_Novelty_AscentCostExponent
import Theorems.Thm_AscentCostLaw_dfsCostB_div_pow_tendsto
import Theorems.Thm_AscentCostLaw_dfsCostB_ge
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

open AscentCostLaw

open Filter Topology

/-! ### The general law -/






/-! ### Asymptotics of the general law -/



/-! ### Two-sided bounds -/



/-! ### The crossover sits at the reciprocal branching factor -/



/-! ### The general exponent law -/






open AscentCostLaw in
theorem solution{b w : ℝ} (hb : 2 ≤ b) (hw : 0 < w) (hwb : w ≤ b - 1) :
    Filter.Tendsto (fun h : ℕ => Real.log (dfsCostB b w h) / h) Filter.atTop (𝓝 (Real.log b)) := by
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (0 : ℝ) < b - 1 := by linarith
  have hCpos : (0 : ℝ) < w * b / (2 * (b - 1) ^ 2) :=
    div_pos (mul_pos hw hb0) (mul_pos (by norm_num) (pow_pos hb1 2))
  have hL : (0 : ℝ) < w * b / (b - 1) ^ 2 := div_pos (mul_pos hw hb0) (pow_pos hb1 2)
  have hg : Filter.Tendsto (fun h : ℕ => dfsCostB b w h / b ^ h) Filter.atTop (𝓝 (w * b / (b - 1) ^ 2)) :=
    dfsCostB_div_pow_tendsto (by linarith) w
  have hlog : Filter.Tendsto (fun h : ℕ => Real.log (dfsCostB b w h / b ^ h)) Filter.atTop
      (𝓝 (Real.log (w * b / (b - 1) ^ 2))) :=
    (Real.continuousAt_log (ne_of_gt hL)).tendsto.comp hg
  have hquot : Filter.Tendsto (fun h : ℕ => Real.log (dfsCostB b w h / b ^ h) / h) Filter.atTop (𝓝 0) :=
    hlog.div_atTop tendsto_natCast_atTop_atTop
  have hlim : Filter.Tendsto (fun h : ℕ => Real.log b + Real.log (dfsCostB b w h / b ^ h) / h) Filter.atTop
      (𝓝 (Real.log b)) := by
    simpa using hquot.const_add (Real.log b)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with h hh
  have hh0 : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hbh : (0 : ℝ) < b ^ h := by positivity
  have hd : 0 < dfsCostB b w h :=
    lt_of_lt_of_le (mul_pos hCpos (pow_pos hb0 h)) (dfsCostB_ge hb hw hwb hh)
  have hsplit : dfsCostB b w h = b ^ h * (dfsCostB b w h / b ^ h) := by field_simp
  rw [hsplit, Real.log_mul (ne_of_gt hbh) (ne_of_gt (div_pos hd hbh)), Real.log_pow, ← hsplit]
  field_simp
