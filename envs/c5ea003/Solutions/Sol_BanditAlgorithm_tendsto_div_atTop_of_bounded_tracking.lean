-- Prove2me | solution 1 for BanditAlgorithm.tendsto_div_atTop_of_bounded_tracking
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T23:19:11.398702+00:00
-- url     : https://prove2.me/submissions/ff4abfe5-8d00-497c-b59b-0b616260f2be

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Definitions.Def_TrackAndStop

/-!
# Elementary algebra of the trajectory statistics

Pull counts, empirical means and empirical allocations, and the identities that
every part of the Track-and-Stop analysis uses:

* `trajPullCount_succ` — the one-round recursion `T_i(t+1) = T_i(t) + 1{A_{t+1} = i}`;
* `sum_trajPullCount` — `∑_i T_i(t) = t`;
* `trajPullCount_le` — `T_i(t) ≤ t`, and monotonicity in `t`;
* `sum_trajAllocation` — the empirical allocation lies in the simplex for `t > 0`;
* `trajEmpiricalMean_eq_zero_of_pullCount_eq_zero` — the junk value convention;
* `trajRewardSum_eq` — `∑ rewards = T_i(t) · μ̂_i(t)` when `T_i(t) > 0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-- The sum of the rewards collected from arm `i` in the first `t` rounds. -/
noncomputable def trajRewardSum (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2

theorem trajEmpiricalMean_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajEmpiricalMean i t ω = trajRewardSum i t ω / (trajPullCount i t ω : ℝ) := rfl

/-! ## Pull counts -/

@[simp]
theorem trajPullCount_zero (i : Fin k) (ω : ℕ → Fin k × ℝ) : trajPullCount i 0 ω = 0 := by
  simp [trajPullCount]

theorem trajPullCount_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i (t + 1) ω =
      trajPullCount i t ω + if (ω t).1 = i then 1 else 0 := by
  classical
  simp only [trajPullCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajRewardSum_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajRewardSum i (t + 1) ω =
      trajRewardSum i t ω + if (ω t).1 = i then (ω t).2 else 0 := by
  classical
  simp only [trajRewardSum, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.sum_insert (by simp), if_pos h, add_comm]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajPullCount_mono (i : Fin k) {s t : ℕ} (h : s ≤ t) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i s ω ≤ trajPullCount i t ω := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact fun x hx ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

theorem trajPullCount_le (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i t ω ≤ t := by
  classical
  calc trajPullCount i t ω ≤ (Finset.range t).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = t := Finset.card_range t

/-- The pull counts of the `k` arms partition the rounds: `∑_i T_i(t) = t`. -/
theorem sum_trajPullCount (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajPullCount i t ω = t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [trajPullCount_succ, Finset.sum_add_distrib, ih]
      congr 1
      simp

/-- Some arm is played at least `t / k` times. -/
theorem exists_trajPullCount_ge (hk : 0 < k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∃ i : Fin k, t ≤ k * trajPullCount i t ω := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i ↦ trajPullCount i t ω) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc t = ∑ j : Fin k, trajPullCount j t ω := (sum_trajPullCount t ω).symm
    _ ≤ ∑ _j : Fin k, trajPullCount i t ω :=
        Finset.sum_le_sum fun j _ ↦ hi j (Finset.mem_univ j)
    _ = k * trajPullCount i t ω := by simp [mul_comm]

/-! ## Empirical allocations -/

@[simp]
theorem trajAllocation_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω = (trajPullCount i t ω : ℝ) / (t : ℝ) := rfl

theorem trajAllocation_nonneg (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajAllocation i t ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem trajAllocation_le_one (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω ≤ 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [trajAllocation]
  · rw [trajAllocation_eq, div_le_one (by exact_mod_cast ht)]
    exact_mod_cast trajPullCount_le i t ω

/-- For `t > 0` the empirical allocation lies in the probability simplex. -/
theorem sum_trajAllocation {t : ℕ} (ht : 0 < t) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajAllocation i t ω = 1 := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  simp only [trajAllocation_eq, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_trajPullCount t ω]
  exact div_self htR

/-! ## Empirical means -/

theorem trajEmpiricalMean_of_pullCount_eq_zero {i : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajPullCount i t ω = 0) : trajEmpiricalMean i t ω = 0 := by
  simp [trajEmpiricalMean, h]

theorem trajRewardSum_eq_mul (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajPullCount i t ω ≠ 0) :
    trajRewardSum i t ω = (trajPullCount i t ω : ℝ) * trajEmpiricalMean i t ω := by
  have hne : ((trajPullCount i t ω : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [trajEmpiricalMean_eq, mul_div_cancel₀ _ hne]

/-! ## The pairwise GLR statistic -/

theorem trajPairGLR_comm (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a b t ω = trajPairGLR b a t ω := by
  simp only [trajPairGLR]
  rw [mul_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    add_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    ← neg_sub (trajEmpiricalMean a t ω) (trajEmpiricalMean b t ω), neg_pow]
  ring

theorem trajPairGLR_nonneg (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajPairGLR a b t ω := by
  refine div_nonneg (mul_nonneg (div_nonneg (mul_nonneg ?_ ?_) ?_) (sq_nonneg _)) (by norm_num)
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · positivity

theorem trajPairGLR_self (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a a t ω = 0 := by
  simp [trajPairGLR]

end BanditAlgorithm

/-!
# Tracking a convergent sequence of allocations

The second half of the D-Tracking analysis (Garivier & Kaufmann, Lemma 8) is a
Cesàro argument and nothing more.  The sampling rule maintains a sequence of
target allocations `p(0), p(1), …` — in Track-and-Stop, `p(s) = α*(μ̂(s))`, which
converges to `α*(μ)` once the empirical means have converged — and plays so that
the realised counts stay within a bounded distance of the cumulative targets:

  `|N_i(t) − ∑_{s < t} p_i(s)| ≤ C`   for all `t`.                        (T)

Then `N_i(t)/t → α_i`, because `(1/t) ∑_{s<t} p_i(s) → α_i` by Cesàro and the
discrepancy `C/t` vanishes.

Only (T) is assumed here; establishing it for a concrete rule is the tracking
lemma proper, and the *other* half of D-Tracking — that no arm is starved — is
`Solutions/ForcedExploration.lean`.  Together they give the hypothesis `htrack`
of the sample-complexity statements.
-/

open Filter Topology

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The abstract statement -/

/-- **Cesàro tracking.**  Counts that stay within a constant of the cumulative
targets inherit the limit of the targets, in the Cesàro sense. -/
theorem tendsto_div_of_tracking {p : ℕ → ℝ} {a C : ℝ}
    (hp : Tendsto p atTop (𝓝 a)) {M : ℕ → ℝ}
    (hbd : ∀ t : ℕ, |M t - ∑ s ∈ Finset.range t, p s| ≤ C) :
    Tendsto (fun t : ℕ ↦ M t / (t : ℝ)) atTop (𝓝 a) := by
  have hces : Tendsto (fun t : ℕ ↦ (∑ s ∈ Finset.range t, p s) / (t : ℝ))
      atTop (𝓝 a) := by
    refine hp.cesaro.congr fun t ↦ ?_
    rw [div_eq_inv_mul]
  -- the discrepancy vanishes
  have hzero : Tendsto (fun t : ℕ ↦
      (M t - ∑ s ∈ Finset.range t, p s) / (t : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat |C|)
    filter_upwards [eventually_gt_atTop 0] with t ht
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos htR]
    exact div_le_div_of_nonneg_right (le_trans (hbd t) (le_abs_self C)) htR.le
  -- and the sum of the two is the quotient we want
  have hsum := hces.add hzero
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have htR : ((t : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    exact this.ne'
  field_simp
  ring

/-! ## The bandit form -/

/-- The version used for the pull counts: `T_i(t)/t → α_i`. -/
theorem tendsto_trajAllocation_of_tracking {p : Fin k → ℕ → ℝ} {α : Fin k → ℝ}
    {C : ℝ} {ω : ℕ → Fin k × ℝ}
    (hp : ∀ i, Tendsto (p i) atTop (𝓝 (α i)))
    (hbd : ∀ i, ∀ t : ℕ,
      |(trajPullCount i t ω : ℝ) - ∑ s ∈ Finset.range t, p i s| ≤ C) :
    ∀ i, Tendsto (fun t : ℕ ↦ trajAllocation i t ω) atTop (𝓝 (α i)) := by
  intro i
  have h := tendsto_div_of_tracking (hp i) (M := fun t ↦ (trajPullCount i t ω : ℝ))
    (hbd i)
  refine h.congr fun t ↦ ?_
  rw [trajAllocation_eq]

/-! ## A sufficient condition for (T): a one-step tracking bound

If at every round the count of the played arm is the one furthest behind its
target, the discrepancy stays bounded; that is the content of the tracking rule.
Recorded here in the weaker form actually needed downstream: a uniform bound on
the discrepancy at every round is enough, however it is obtained. -/

/-- Discrepancies that are bounded at each round are bounded uniformly by the
supremum, so (T) is exactly a uniform-boundedness statement. -/
theorem tracking_of_forall_le {p : Fin k → ℕ → ℝ} {C : ℝ} {ω : ℕ → Fin k × ℝ}
    (h : ∀ i t, |(trajPullCount i t ω : ℝ) - ∑ s ∈ Finset.range t, p i s| ≤ C)
    (i : Fin k) (t : ℕ) :
    |(trajPullCount i t ω : ℝ) - ∑ s ∈ Finset.range t, p i s| ≤ C := h i t

/-! ## Convergence of the targets from convergence of the means

In Track-and-Stop the targets are `p(s) = choice(μ̂(s))`, so their convergence
follows from that of the empirical means together with continuity of the map
`choice` at `μ`.  Continuity is genuinely needed: `choice` is only required to
*select* an optimal allocation, and a selection that jumps cannot be tracked. -/

theorem tendsto_targets_of_continuousAt {choice : (Fin k → ℝ) → Fin k → ℝ}
    {μvec : Fin k → ℝ} {m : ℕ → Fin k → ℝ}
    (hcont : ContinuousAt choice μvec)
    (hm : Tendsto m atTop (𝓝 μvec)) (i : Fin k) :
    Tendsto (fun s ↦ choice (m s) i) atTop (𝓝 (choice μvec i)) := by
  have h : Tendsto (fun s ↦ choice (m s)) atTop (𝓝 (choice μvec)) :=
    hcont.tendsto.comp hm
  exact (continuous_apply i).continuousAt.tendsto.comp h

end BanditAlgorithm

theorem _root_.solution {p : ℕ → ℝ} {a C : ℝ}
    (hp : Filter.Tendsto p Filter.atTop (nhds a)) (M : ℕ → ℝ)
    (hbd : ∀ t : ℕ, |M t - ∑ s ∈ Finset.range t, p s| ≤ C) :
    Filter.Tendsto (fun t : ℕ ↦ M t / (t : ℝ)) Filter.atTop (nhds a) :=
  BanditAlgorithm.tendsto_div_of_tracking hp hbd
