-- Prove2me | Definitions.Def_Combinatorics_KneeQuantile
-- name    : Combinatorics_KneeQuantile
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:33.716833+00:00
-- url     : https://prove2.me/theorems/40dff9c7-ae28-4f5b-a2e4-d0db325dcc30
-- title:
--   Aether Catalog definitions — Combinatorics_KneeQuantile
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.KneeQuantile`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/KneeQuantile.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance

/-!
# The knee is an order statistic (NET-70, cycle 3)

Cycle 1 showed that the NET-70 knee only sees the *demand multiset*; cycle 2
turned the deployment table into an interval point-cover.  This file explains
**why** the knee is so stable across domains — stable enough to survive a
12-point accuracy gap — by identifying it exactly:

> `knee = the ⌈g·n⌉-th smallest demand`.

An order statistic, not an average.  Consequences proved here:

* `knee_eq_demandQuantile` — the identity itself.
* `knee_le_iff_tail_small` — the **exact gate criterion**: `k` clears the gate
  iff at most `(1-g)·n` windows demand more than `k` keys.  Markov's bound
  (`knee_le_of_markov`) is the one-sided relaxation of this.
* `knee_le_of_tail_zero`, `knee_pos_of_tail_large` — the two directions in
  usable form.
* `knee_permutation_invariant` — relabelling windows cannot move the knee;
  combined with `knee_eq_of_demandMultiset_eq` this says the sweep is a
  *symmetric function of the demands only*.
* `knee_stable_under_bounded_perturbation` — **robustness**: perturbing the
  demand of at most `(1-g)·n - tail` windows arbitrarily (e.g. the hardest
  windows of a harder domain) cannot raise the knee above `k`.  This is the
  structural reason a domain jump that costs 12 accuracy points can still leave
  the knee exactly where it was: accuracy is an average over all windows, the
  knee is a quantile of a different statistic.
-/

namespace Combinatorics.KneeQuantile

open Finset Combinatorics.KneeInvariance

variable {n : ℕ}

/-- The `m`-th smallest demand of a workload (`m` counted from 1), as the least
budget serving at least `m` windows. -/
noncomputable def demandQuantile (D : Workload n) (m : ℕ) : ℕ :=
  sInf {k | m ≤ agreeCount D k}







end Combinatorics.KneeQuantile


