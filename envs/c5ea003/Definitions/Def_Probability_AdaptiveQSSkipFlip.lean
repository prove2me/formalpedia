-- Prove2me | Definitions.Def_Probability_AdaptiveQSSkipFlip
-- name    : Probability_AdaptiveQSSkipFlip
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:36.004834+00:00
-- url     : https://prove2.me/theorems/5d3eca54-0347-42e0-b028-cf21749fa03b
-- title:
--   Aether Catalog definitions — Probability_AdaptiveQSSkipFlip
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AdaptiveQSSkipFlip`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AdaptiveQSSkipFlip.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Skip-flip wins, and the quadratic-residue null equaliser

Companion to `Probability.AdaptiveQSAllocation`.  That file shows that spending a
*fixed* budget in inverse proportion to a predicted rate must lose.  Experiment 559
then flipped the deployment: instead of reallocating sieve length, use the same
dial to **skip** the worst targets (`θ = q20` skipped `28.3%` of the work while
retaining `89.5%` of the relations, a `+28.9%` throughput gain), and defer the hard
tail (`40/400` targets that no amount of sieving reaches).

This file proves that the flip is not a lucky calibration but a theorem, in three
layers.

1. **Separation ⇒ retention beats work fraction.**  `sum_le_of_separated_slack` is
   the general engine: if every kept target beats every skipped target up to a slack
   `c`, then `|K| · (total yield) ≤ |s| · (kept yield) + c |K| |D|`.  With `c = 0`
   (`retention_ge_work_fraction`) this says exactly `retention ≥ work fraction`, i.e.
   the throughput ratio is `≥ 1`; `skip_throughput_ge` and `skip_throughput_gt` state
   it as a mean comparison, the latter strictly.

2. **An imperfect dial still wins, quantitatively.**  `approx_dial_retention` runs
   the same engine with `c = 2ε` for a dial that is only `ε`-accurate — the measured
   Spearman `0.739 < 1` costs at most a `2ε` degradation term, and
   `approx_dial_threshold_gain` gives the explicit condition on `ε` under which the
   skip still wins.  This is the robustness statement the deployment needs.

3. **The null equaliser is exact arithmetic, not statistics.**  A prime `p` for which
   `N` is a quadratic *non*-residue divides **no** value `x² - N`
   (`nonresidue_not_dvd_qsValue`), so its sieve hit rate is identically zero
   (`hitRate_eq_zero_of_nonresidue`) — the hard tail is unreachable by construction.
   `qs_null_equalizer` then says the yield of *any* allocation is unchanged by
   deleting the null targets, and `transfer_from_null_lt` says that moving any
   positive amount of budget off a null target onto a live one strictly increases the
   yield.  Deferral, not deeper sieving, is the instrument.
-/

namespace Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The separation engine -/




/-! ## The deployment flip: threshold skipping -/

/-- The targets kept by a dial threshold. -/
noncomputable def keepSet (s : Finset ι) (d : ι → ℝ) (θ : ℝ) : Finset ι :=
  s.filter (fun i => θ ≤ d i)

/-- The targets deferred by a dial threshold. -/
noncomputable def skipSet (s : Finset ι) (d : ι → ℝ) (θ : ℝ) : Finset ι :=
  s.filter (fun i => ¬ θ ≤ d i)

/-- Yield per unit of work of a set of targets, all sieved at the same length. -/
noncomputable def throughput (K : Finset ι) (r : ι → ℝ) : ℝ := (∑ i ∈ K, r i) / K.card



/-- A dial is **concordant** with the true rate on `s` when it never orders two targets
backwards: a strictly smaller dial reading means a no-larger rate. -/
def Concordant (s : Finset ι) (d r : ι → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, d j < d i → r j ≤ r i






/-! ## An imperfect dial: the quantitative flip -/



/-! ## The quadratic-residue null equaliser -/

section NullEqualizer

omit [DecidableEq ι]

/-- The quadratic-sieve value at `x` for the target `N`. -/
def qsValue (N x : ℤ) : ℤ := x ^ 2 - N


/-- The empirical hit rate of the prime `p` in the sieve window `w`. -/
noncomputable def hitRate (N : ℤ) (w : Finset ℤ) (p : ℕ) : ℝ :=
  ((w.filter (fun x => (p : ℤ) ∣ qsValue N x)).card : ℝ) / w.card



end NullEqualizer

/-- Transferring budget from one target to another. -/
noncomputable def transfer (ℓ : ι → ℝ) (a b : ι) (δ : ℝ) : ι → ℝ :=
  fun i => if i = a then ℓ a - δ else if i = b then ℓ b + δ else ℓ i


end Probability.AdaptiveQS


