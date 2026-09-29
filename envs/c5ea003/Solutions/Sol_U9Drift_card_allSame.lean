-- Prove2me | solution 1 for U9Drift.card_allSame
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:42:54.586301+00:00
-- url     : https://prove2.me/submissions/63eba4c1-baa7-47b9-8339-e2f612979560

-- Sol generated from Probability/U9DriftPower.lean
import Mathlib
import Definitions.Def_Probability_U9DriftIntervals
import Definitions.Def_Probability_U9DriftPower
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Power arithmetic for the band-9 replication: how many clusters, and what a
  direction-stable split-half is worth

Context (experiment 569, paper 216).  Two quantitative claims of the round-74 ledger are
audited here.

**(1) "Decisive resolution still needs the 10–30× power run."**  A cluster bootstrap over
`m` independent `N`-clusters has half width `c/√m` for a calibration constant `c` fixed by
the per-cluster dispersion; the realised run had `m = 128` clusters and half width
`0.04555`, which calibrates `c = 0.04555·√128`.  To make the interval exclude `1` at the
replication's own point estimate `0.99`, the half width must drop below `0.01`.

* `U9Drift.ten_times_the_clusters_is_not_enough` — `10×` the clusters (`m ≤ 1280`) provably
  cannot get there;
* `U9Drift.thirty_times_the_clusters_suffices` — `30×` the clusters (`m ≥ 3840`) provably
  does.

So the ledger's "10–30×" ask is exactly right, and the interval `[10×, 30×]` is the
narrowest decade-scale bracket consistent with the `√m` law (the exact threshold is
`m ≥ 2656`, `U9Drift.exact_cluster_threshold`).

**(2) "Every CI covers 1 but every split-half points the same way."**  Under the null the
sign of each split-half is a fair coin, so `k` split-halves agreeing has probability
`2^{1-k}`:

* `U9Drift.card_allSame` / `U9Drift.direction_stability_pvalue` — exactly `2` of the `2^k`
  sign patterns are constant;
* `U9Drift.four_split_halves_are_not_significant` — with `k = 4` the null probability is
  `1/8`, well above `0.05`: direction stability at that depth is *not* evidence;
* `U9Drift.split_halves_needed_for_significance` — one needs `k ≥ 6` agreeing split-halves
  before the sign test even reaches the `5%` level.

Finally `U9Drift.pilot_effect_size_would_have_been_resolved` records the diagnostic
consequence: the replication's precision `0.04555` was already fine enough that a true
ratio at the pilot's point estimate `0.947` would have produced an interval excluding `1`.
-/

open U9Drift

open Real Finset

/-! ## The `√m` cluster-bootstrap scaling law -/






/-! ## Calibration from the realised run -/









/-! ## What a direction-stable split-half is worth -/








open U9Drift in
theorem solution{k : ℕ} (hk : 0 < k) : (allSame k).card = 2 := by
  have hset : allSame k = {fun _ => false, fun _ => true} := by
    ext f
    simp only [allSame, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro h
      rcases Bool.eq_false_or_eq_true (f ⟨0, hk⟩) with hb | hb
      · right; funext i; rw [h i ⟨0, hk⟩, hb]
      · left; funext i; rw [h i ⟨0, hk⟩, hb]
    · rintro (rfl | rfl) <;> intro i j <;> rfl
  have hne : (fun _ => false : Fin k → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h ⟨0, hk⟩
    simp at this
  rw [hset, card_insert_of_notMem (by simpa using hne), card_singleton]
