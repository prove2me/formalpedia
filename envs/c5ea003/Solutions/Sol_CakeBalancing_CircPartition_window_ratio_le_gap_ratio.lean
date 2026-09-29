-- Prove2me | solution 1 for CakeBalancing.CircPartition.window_ratio_le_gap_ratio
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:15:05.708356+00:00
-- url     : https://prove2.me/submissions/88be4ee1-5554-4046-8fef-9437ee6bff38

-- Sol generated from Applications/CakeBalancingRatio/Core.lean
import Mathlib
import Definitions.Def_Applications_CakeBalancingRatio_Core

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

open CakeBalancing

open Finset


open CircPartition

variable (P : CircPartition)









/-- The gap sequence depends only on the index modulo the period. -/
lemma g_mod (i : ℕ) : P.g i = P.g (i % P.n) := by
  have hp : Function.Periodic P.g P.n := fun x => P.periodic x
  simpa using (hp.map_mod_nat i).symm

/-- Every gap is at most the maximum gap. -/
lemma g_le_maxgap (i : ℕ) : P.g i ≤ P.maxgap := by
  rw [g_mod P i, maxgap]
  exact Finset.le_sup' P.g (mem_range.mpr (Nat.mod_lt i P.npos))

/-- Every gap is at least the minimum gap. -/
lemma mingap_le_g (i : ℕ) : P.mingap ≤ P.g i := by
  rw [g_mod P i, mingap]
  exact Finset.inf'_le P.g (mem_range.mpr (Nat.mod_lt i P.npos))

/-- The minimum gap is positive. -/
lemma mingap_pos : 0 < P.mingap := by
  rw [mingap, Finset.lt_inf'_iff]
  intro i _; exact P.pos i

/-- Balance is nontrivial: minimum gap does not exceed maximum gap. -/
lemma mingap_le_maxgap : P.mingap ≤ P.maxgap := by
  rw [maxgap, mingap]
  obtain ⟨a, ha⟩ := P.range_nonempty
  exact le_trans (Finset.inf'_le P.g ha) (Finset.le_sup' P.g ha)

/-- The maximum gap is positive. -/
lemma maxgap_pos : 0 < P.maxgap := lt_of_lt_of_le (mingap_pos P) (mingap_le_maxgap P)


/-- An `r`-window sum is at most `r` times the maximum gap. -/
lemma W_le_r_mul_maxgap (r i : ℕ) : P.W r i ≤ (r : ℝ) * P.maxgap := by
  rw [W]
  calc ∑ j ∈ range r, P.g (i + j) ≤ ∑ _j ∈ range r, P.maxgap :=
        Finset.sum_le_sum (fun j _ => g_le_maxgap P (i + j))
    _ = (r : ℝ) * P.maxgap := by rw [Finset.sum_const, card_range]; ring

/-- An `r`-window sum is at least `r` times the minimum gap. -/
lemma r_mul_mingap_le_W (r i : ℕ) : (r : ℝ) * P.mingap ≤ P.W r i := by
  rw [W]
  calc (r : ℝ) * P.mingap = ∑ _j ∈ range r, P.mingap := by
          rw [Finset.sum_const, card_range]; ring
    _ ≤ ∑ j ∈ range r, P.g (i + j) := Finset.sum_le_sum (fun j _ => mingap_le_g P (i + j))

/-- The maximum window sum is at most `r` times the maximum gap. -/
lemma maxwin_le_r_mul_maxgap (r : ℕ) : P.maxwin r ≤ (r : ℝ) * P.maxgap := by
  rw [maxwin]; exact Finset.sup'_le _ _ (fun i _ => W_le_r_mul_maxgap P r i)

/-- The minimum window sum is at least `r` times the minimum gap. -/
lemma r_mul_mingap_le_minwin (r : ℕ) : (r : ℝ) * P.mingap ≤ P.minwin r := by
  rw [minwin]; exact Finset.le_inf' _ _ (fun i _ => r_mul_mingap_le_W P r i)

/-- For `r ≥ 1` the minimum window sum is positive. -/
lemma minwin_pos {r : ℕ} (hr : 1 ≤ r) : 0 < P.minwin r := by
  have h0 : 0 < r := hr
  have hpos : (0 : ℝ) < (r : ℝ) * P.mingap := by
    have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h0
    have := mingap_pos P; positivity
  exact lt_of_lt_of_le hpos (r_mul_mingap_le_minwin P r)





/-! ## The uniform partition -/



/-! ## The de Bruijn–Erdős three-point van der Corput partition -/






open CakeBalancing in
theorem solution{r : ℕ} (hr : 1 ≤ r) :
    P.winRatio r ≤ P.gapRatio := by
  have h0 : 0 < r := hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h0
  have hmaxg : (0 : ℝ) ≤ P.maxgap := le_of_lt (maxgap_pos P)
  have hmnpos : 0 < P.minwin r := minwin_pos P hr
  have hmw : P.maxwin r ≤ (r : ℝ) * P.maxgap := maxwin_le_r_mul_maxgap P r
  have hmg : (r : ℝ) * P.mingap ≤ P.minwin r := r_mul_mingap_le_minwin P r
  have hrmin : (0 : ℝ) < (r : ℝ) * P.mingap := by have := mingap_pos P; positivity
  rw [winRatio, gapRatio]
  calc P.maxwin r / P.minwin r
      ≤ ((r : ℝ) * P.maxgap) / P.minwin r := by gcongr
    _ ≤ ((r : ℝ) * P.maxgap) / ((r : ℝ) * P.mingap) := by gcongr
    _ = P.maxgap / P.mingap := by rw [mul_div_mul_left _ _ (ne_of_gt hrpos)]
