-- Prove2me | Definitions.Def_Applications_CakeBalancingRatio_Core
-- name    : Applications_CakeBalancingRatio_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:15.035987+00:00
-- url     : https://prove2.me/theorems/0d9bfa9a-0a2e-4584-8c00-8b76ab478cb4
-- title:
--   Aether Catalog definitions — Applications_CakeBalancingRatio_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CakeBalancingRatio.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CakeBalancingRatio/Core.lean by skeleton subtraction
import Mathlib

/-!
# Balancing ratios of circular partitions — Core

This file develops the structural core behind the *cake balancing ratio sequence*
studied in the mission "Upper bound conjecture for the cake balancing ratio
sequence" (in the spirit of de Bruijn–Erdős cake cutting and discrepancy theory
for circular partitions).

## Setting

A sequence of points placed on a circle cuts it into arcs.  We model a *cyclic
partition* by its sequence of **gap lengths** `g : ℕ → ℝ`, positive and periodic
with period `n` (so the circle carries `n` distinct arcs `g 0, …, g (n-1)`,
repeated cyclically).  For a window length `r ≥ 1`, the **`r`-window sum**
starting at position `i` is the length of `r` consecutive arcs,
`W r i = g i + g (i+1) + ⋯ + g (i+r-1)`.

The **single-gap ratio** is `gapRatio = maxgap / mingap`, and the
**`r`-window ratio** is `winRatio r = maxwin r / minwin r`, where the extrema
range over the `n` cyclic starting positions.  These are the finite-stage
quantities `μ¹_n` and `μ^r_n` from the mission statement.

## Main results

* `mingap_le_maxgap`, `one_le_gapRatio` : the ratio is always `≥ 1`.
* `window_ratio_le_gap_ratio` : `winRatio r ≤ gapRatio` for every `r ≥ 1`.
  Aggregating `r` consecutive arcs can only *improve* balance — the key
  structural monotonicity behind the `2r/p + 1` upper-bound conjecture.
* `one_le_winRatio` : `winRatio r ≥ 1`.
* `winRatio_uniform_eq_one` : the equal-arc partition has every window ratio `1`.
* `vdc3_gapRatio_eq_two` : the de Bruijn–Erdős three-point van der Corput
  partition `{1/4, 1/4, 1/2}` realises single-gap ratio exactly `2`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  The mission conjecture `μ_r^σ ≤ 2r/p + 1` predicts
that window ratios grow at most linearly in `r`.  A necessary structural fact
underneath any such bound is that *windowing cannot make balance worse*: since
each `r`-window sum lies between `r·mingap` and `r·maxgap`, the window ratio is
squeezed below the raw gap ratio.  We conjecture `winRatio r ≤ gapRatio` for all
`r`, unconditionally.

EXPERIMENT (Experimenter).  Proven below via the two envelope bounds
`maxwin_le_r_mul_maxgap` and `r_mul_mingap_le_minwin`, then a division estimate.

ANALYSIS (Analyst).  The bound is *exact at `r = 1`* and *tight for the uniform
partition* (ratio `1` at every `r`).  The van der Corput example shows the raw
ratio `2` is attainable, matching the de Bruijn–Erdős cake-cutting benchmark.

CRITIQUE (Critic).  Positivity of `mingap` (hence of `minwin`) is load-bearing;
every division lemma carries the `r ≥ 1` hypothesis so denominators stay
positive.  No statement is vacuous: the uniform and van der Corput witnesses
show the extremal values `1` and `2` are attained.

SYNTHESIS (PI).  `winRatio r ≤ gapRatio` is the monotone scaffold on which the
full `2r/p + 1` recipe bound should rest; see `FUTURE_DIRECTIONS.md`.
-/

namespace CakeBalancing

open Finset

/-- A cyclic partition of a circle into `n` positive arcs, described by its
periodic sequence of gap lengths. -/
structure CircPartition where
  /-- number of arcs -/
  n : ℕ
  /-- there is at least one arc -/
  npos : 0 < n
  /-- gap length sequence -/
  g : ℕ → ℝ
  /-- all arcs have positive length -/
  pos : ∀ i, 0 < g i
  /-- the arc pattern repeats with period `n` -/
  periodic : ∀ i, g (i + n) = g i

namespace CircPartition

variable (P : CircPartition)

/-- The index set of cyclic starting positions is nonempty. -/
lemma range_nonempty : (range P.n).Nonempty := nonempty_range_iff.mpr P.npos.ne'

/-- Largest single arc length. -/
noncomputable def maxgap : ℝ := (range P.n).sup' P.range_nonempty P.g

/-- Smallest single arc length. -/
noncomputable def mingap : ℝ := (range P.n).inf' P.range_nonempty P.g

/-- Sum of `r` consecutive arcs starting at position `i`. -/
noncomputable def W (r i : ℕ) : ℝ := ∑ j ∈ range r, P.g (i + j)

/-- Largest `r`-window sum over the `n` cyclic starting positions. -/
noncomputable def maxwin (r : ℕ) : ℝ := (range P.n).sup' P.range_nonempty (fun i => P.W r i)

/-- Smallest `r`-window sum over the `n` cyclic starting positions. -/
noncomputable def minwin (r : ℕ) : ℝ := (range P.n).inf' P.range_nonempty (fun i => P.W r i)

/-- Single-gap ratio `μ¹_n`. -/
noncomputable def gapRatio : ℝ := P.maxgap / P.mingap

/-- `r`-window ratio `μ^r_n`. -/
noncomputable def winRatio (r : ℕ) : ℝ := P.maxwin r / P.minwin r
















end CircPartition

/-! ## The uniform partition -/

/-- The perfectly balanced partition into `n` equal arcs of length `1/n`. -/
noncomputable def uniform (n : ℕ) (hn : 0 < n) : CircPartition where
  n := n
  npos := hn
  g := fun _ => 1 / n
  pos := fun _ => by positivity
  periodic := fun _ => rfl


/-! ## The de Bruijn–Erdős three-point van der Corput partition -/

/-- The three-arc partition `{1/4, 1/4, 1/2}` obtained from the first three
points of the base-2 van der Corput sequence. -/
noncomputable def vdc3 : CircPartition where
  n := 3
  npos := by norm_num
  g := fun i => if i % 3 = 2 then (1 : ℝ) / 2 else 1 / 4
  pos := fun i => by split <;> norm_num
  periodic := fun i => by simp only [Nat.add_mod_right]




end CakeBalancing


