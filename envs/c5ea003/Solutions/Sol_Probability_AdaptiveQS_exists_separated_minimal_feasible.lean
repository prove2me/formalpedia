-- Prove2me | solution 1 for Probability.AdaptiveQS.exists_separated_minimal_feasible
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:23:32.884447+00:00
-- url     : https://prove2.me/submissions/27ad582e-21e7-4129-9280-7893995915ea

-- Sol generated from Probability/AdaptiveQSPrefixOptimality.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSPrefixOptimality
import Definitions.Def_Probability_AdaptiveQSSkipFlip
import Theorems.Thm_Probability_AdaptiveQS_separated_of_max_sum
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Prefix optimality of deferral under a relation quota

Experiment 559 (round-73 #2, `ADAPT-NULL-EQUALIZER / SKIP-FLIP-WINS`) ended with the
deployment recommendation *defer, don't sieve deeper*: a dial threshold `θ = q20` skipped
`28.3%` of the work while retaining `89.5%` of the relations.  `AdaptiveQSSkipFlip.lean`
proved the sign of that flip (throughput never falls, and strictly rises once a genuinely
worse target is deferred), and `AdaptiveQSThresholdTradeoff.lean` proved the honest
boundary (total retained yield falls with the threshold).

What was left open — and is what a deployment actually has to decide — is the *policy
space*: the sieve must collect a quota `Q` of relations, and one may in principle pick any
subset `K ⊆ s` of targets to work on.  This file closes that question:

* `exists_max_sum_card_subset` — a maximal-yield subset of each fixed cardinality exists;
* `separated_of_max_sum` — **every** such maximiser is *separated*: each retained target
  beats every deferred one.  This is an exchange argument, and it is the reason a sort is
  enough: no maximiser can be "interleaved" with the deferred set.
* `exists_separated_of_quota` — any quota-feasible schedule is dominated, at the same cost,
  by a separated one;
* `exists_separated_minimal_feasible` — the **minimum-work** quota-feasible schedule can
  always be taken separated;
* `separated_subset_keepSet`, `keepSet_sum_ge_of_separated` — a separated set is contained
  in a dial threshold set `keepSet s r θ` at `θ = min` of its own rates, and that threshold
  set is again quota-feasible;
* `quota_threshold_policy` — the capstone: whenever the quota is attainable at all, it is
  attained by a *single threshold* on the rate dial, and that threshold policy has
  throughput at least that of sieving everything.

So the deployment's policy space collapses from `2^|s|` subsets to one real number: the
skip-flip's `θ` is not just a good heuristic, it is the shape of the optimum.  The
hypotheses are exactly "rates are nonnegative" — no calibration, no independence.
-/

open Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## Separated schedules -/


omit [DecidableEq ι] in
/-- **Existence of a best schedule of a given size.**  Among the (finitely many) subsets of
`s` with exactly `k` targets there is one of maximal total rate. -/
theorem exists_max_sum_card_subset (s : Finset ι) (r : ι → ℝ) {k : ℕ} (hk : k ≤ s.card) :
    ∃ T ⊆ s, T.card = k ∧ ∀ K ⊆ s, K.card = k → ∑ i ∈ K, r i ≤ ∑ i ∈ T, r i := by
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (s.powersetCard k) (fun T => ∑ i ∈ T, r i)
      (Finset.powersetCard_nonempty.mpr hk)
  rw [Finset.mem_powersetCard] at hT
  exact ⟨T, hT.1, hT.2, fun K hKs hKc => hmax K (Finset.mem_powersetCard.mpr ⟨hKs, hKc⟩)⟩


/-! ## Quota feasibility -/

omit [DecidableEq ι] in
/-- **Any schedule is dominated by a separated one of the same cost.**  If some set of `k`
targets collects the quota `Q`, then the best set of `k` targets does too, and it is
separated. -/
theorem exists_separated_of_quota {s K : Finset ι} {r : ι → ℝ} {Q : ℝ}
    (hKs : K ⊆ s) (hQ : Q ≤ ∑ i ∈ K, r i) :
    ∃ T ⊆ s, T.card = K.card ∧ Q ≤ ∑ i ∈ T, r i ∧ Separated s T r := by
  obtain ⟨T, hTs, hTc, hTmax⟩ :=
    exists_max_sum_card_subset s r (k := K.card) (Finset.card_le_card hKs)
  classical
  refine ⟨T, hTs, hTc, le_trans hQ (hTmax K hKs rfl), ?_⟩
  exact separated_of_max_sum hTs (by rw [hTc]; exact hTmax)


/-! ## A separated schedule is a dial threshold -/





/-! ## Lab notes — a machine-checked three-target instance

Rates `r = (3, 1, 0)` on `s = {0, 1, 2} ⊆ ℕ` with quota `Q = 3`.  The minimum-work feasible
schedule is the single top target `{0}`: one target instead of three, i.e. `66.7%` of the
work deferred at `100%` of the quota, and the throughput rises from `4/3` to `3`.  Every
number below is proved, not asserted. -/





open Probability.AdaptiveQS in
omit [DecidableEq ι] in
theorem solution{s : Finset ι} {r : ι → ℝ} {Q : ℝ}
    (hfeas : ∃ K ⊆ s, Q ≤ ∑ i ∈ K, r i) :
    ∃ T ⊆ s, Q ≤ ∑ i ∈ T, r i ∧ Separated s T r ∧
      ∀ K ⊆ s, Q ≤ ∑ i ∈ K, r i → T.card ≤ K.card := by
  classical
  set P : ℕ → Prop := fun n => ∃ K ⊆ s, K.card = n ∧ Q ≤ ∑ i ∈ K, r i with hP
  have hex : ∃ n, P n := by
    obtain ⟨K, hKs, hKQ⟩ := hfeas
    exact ⟨K.card, K, hKs, rfl, hKQ⟩
  obtain ⟨K, hKs, hKc, hKQ⟩ : P (Nat.find hex) := Nat.find_spec hex
  obtain ⟨T, hTs, hTc, hTQ, hTsep⟩ := exists_separated_of_quota hKs hKQ
  refine ⟨T, hTs, hTQ, hTsep, ?_⟩
  intro K' hK's hK'Q
  have hmin : Nat.find hex ≤ K'.card := Nat.find_min' hex ⟨K', hK's, rfl, hK'Q⟩
  omega
