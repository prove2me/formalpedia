-- Prove2me | solution 2 for BanditAlgorithm.chernoff_stopping_time_le_integrable_plus_linear_of_settling_time
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T23:21:54.037671+00:00
-- url     : https://prove2.me/submissions/80ba89dd-a77a-485f-a479-8c1cd9d1b385

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Measurability of the Track-and-Stop trajectory statistics

Everything Algorithm 21 computes at the end of round `t` is a function of the
first `t` rounds, hence `banditFiltration k t`-measurable.  This file proves that,
for each statistic of `Def_TrackAndStop`, and deduces the two structural clauses
of L&S Lemma 33.7:

* `isBanditStoppingTime_chernoffStoppingTime` — Chernoff's rule really is a
  stopping time of the natural filtration;
* `measurable_chernoffRecommendation` — the recommended arm is measurable with
  respect to the stopping-time σ-algebra `𝓕_τ`.

The only delicate point is that `trajEmpiricalBestArm` is defined through
`Finset.exists_max_image`, i.e. through `Classical.choose`, which carries no
measurability whatsoever.  It is handled in §3: we introduce the *canonical*
(least-index) maximiser `trajArgmax`, which is manifestly measurable, and show
that `trajGLR` — the only consumer of `trajEmpiricalBestArm` — is unchanged when
the canonical maximiser is substituted.  The proof splits on whether the maximum
is attained twice: if it is, both versions of `trajGLR` vanish (the pair term for
the two tied maximisers is `0`), and if it is not, the two maximisers coincide.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Generic comap measurability -/

/-- `Nat.cast : ℕ → ℝ` is measurable (source σ-algebra is `⊤`). -/
theorem measurable_natCast_real : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
  measurable_from_top


/-- A function that factors through `g` is measurable for the σ-algebra `g`
pulls back. -/
theorem measurable_comap_comp {α β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {g : α → β} {f : β → γ} (hf : Measurable f) :
    Measurable[MeasurableSpace.comap g inferInstance] (fun a ↦ f (g a)) :=
  fun _ hs ↦ ⟨f ⁻¹' _, hf hs, rfl⟩

/-- The coordinate `ω s` is `𝓕_t`-measurable as soon as round `s` is among the
first `t`. -/
theorem measurable_trajCoord {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ ω s) := by
  have : (fun ω : ℕ → Fin k × ℝ ↦ ω s) =
      (fun h : BanditHistory k t ↦ h ⟨s, hs⟩) ∘ banditTrajPrefix k t := rfl
  rw [this]
  exact measurable_comap_comp (measurable_pi_apply _)

/-- The arm played in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajArm {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).1) :=
  measurable_fst.comp (measurable_trajCoord hs)

/-- The reward observed in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajReward {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).2) :=
  measurable_snd.comp (measurable_trajCoord hs)

/-! ## 2. The elementary statistics -/

/-- `T_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajPullCount (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPullCount i t) := by
  classical
  -- the count is a finite sum of indicators of `𝓕_t`-measurable events
  have hrw : trajPullCount i t =
      fun ω : ℕ → Fin k × ℝ ↦ ∑ s ∈ Finset.range t, if (ω s).1 = i then 1 else 0 := by
    funext ω
    rw [trajPullCount, Finset.card_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_trajArm hs') (measurableSet_singleton i)

/-- The running sum of the rewards collected from arm `i` is `𝓕_t`-measurable. -/
theorem measurable_trajRewardSum (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) := by
  classical
  have hrw : (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) =
      fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ Finset.range t, if (ω s).1 = i then (ω s).2 else 0 := by
    funext ω
    rw [Finset.sum_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  exact Measurable.ite ((measurable_trajArm hs') (measurableSet_singleton i))
    (measurable_trajReward hs') measurable_const

/-- `μ̂_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajEmpiricalMean (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajEmpiricalMean i t) := by
  have hrw : trajEmpiricalMean i t = fun ω : ℕ → Fin k × ℝ ↦
      (∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) /
        ((trajPullCount i t ω : ℕ) : ℝ) := rfl
  rw [hrw]
  exact (measurable_trajRewardSum i t).div
    (measurable_natCast_real.comp (measurable_trajPullCount i t))

/-- `T_i(t)/t` is `𝓕_t`-measurable. -/
theorem measurable_trajAllocation (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajAllocation i t) := by
  have hrw : trajAllocation i t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount i t ω : ℕ) : ℝ) / (t : ℝ) := rfl
  rw [hrw]
  exact (measurable_natCast_real.comp (measurable_trajPullCount i t)).div measurable_const

/-- The pairwise GLR statistic is `𝓕_t`-measurable. -/
theorem measurable_trajPairGLR (a b : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPairGLR a b t) := by
  have hrw : trajPairGLR a b t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount a t ω : ℕ) : ℝ) * ((trajPullCount b t ω : ℕ) : ℝ) /
          (((trajPullCount a t ω : ℕ) : ℝ) + ((trajPullCount b t ω : ℕ) : ℝ)) *
        (trajEmpiricalMean a t ω - trajEmpiricalMean b t ω) ^ 2 / 2 := rfl
  rw [hrw]
  have hTa : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount a t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount a t)
  have hTb : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount b t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount b t)
  exact ((((hTa.mul hTb).div (hTa.add hTb)).mul
    (((measurable_trajEmpiricalMean a t).sub
      (measurable_trajEmpiricalMean b t)).pow_const 2)).div measurable_const)

/-! ## 3. The canonical maximiser and tie-independence of `Z_t` -/

section Argmax

variable [NeZero k]

/-- The *canonical* empirical best arm: the least index at which the empirical
mean is maximal.  Unlike `trajEmpiricalBestArm`, which is defined through
`Classical.choose`, this one is measurable. -/
noncomputable def trajArgmax (t : ℕ) (ω : ℕ → Fin k × ℝ) : Fin k :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω).min'
    (by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
        (fun i ↦ trajEmpiricalMean i t ω) Finset.univ_nonempty
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j ↦ hi j (Finset.mem_univ j)⟩⟩)

theorem trajArgmax_mem_filter (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajArgmax t ω ∈ (Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω :=
  Finset.min'_mem _ _

/-- `trajArgmax` is a maximiser. -/
theorem trajArgmax_spec (t : ℕ) (ω : ℕ → Fin k × ℝ) (j : Fin k) :
    trajEmpiricalMean j t ω ≤ trajEmpiricalMean (trajArgmax t ω) t ω :=
  (Finset.mem_filter.mp (trajArgmax_mem_filter t ω)).2 j

/-- `trajArgmax` is the *least* maximiser. -/
theorem trajArgmax_le (t : ℕ) (ω : ℕ → Fin k × ℝ) {i : Fin k}
    (hi : ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω) :
    trajArgmax t ω ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- The canonical maximiser is measurable: its level sets are cut out by finitely
many inequalities between the (measurable) empirical means. -/
theorem measurable_trajArgmax (t : ℕ) :
    Measurable[banditFiltration k t] (trajArgmax (k := k) t) := by
  classical
  have hle : ∀ a b : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | trajEmpiricalMean a t ω ≤ trajEmpiricalMean b t ω} := fun a b ↦
    measurableSet_le (measurable_trajEmpiricalMean a t) (measurable_trajEmpiricalMean b t)
  have hmax : ∀ i : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
    intro i
    have hrw : {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω}
        = ⋂ j : Fin k,
          {ω : ℕ → Fin k × ℝ | trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
      ext ω; simp
    rw [hrw]
    exact MeasurableSet.iInter fun j ↦ hle j i
  refine @measurable_to_countable' (Fin k) _ _ _ (banditFiltration k t) _ fun i ↦ ?_
  have hset : (trajArgmax (k := k) t) ⁻¹' {i} =
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} ∩
        ⋂ j ∈ {j : Fin k | j < i},
          {ω : ℕ → Fin k × ℝ | ∀ l, trajEmpiricalMean l t ω ≤ trajEmpiricalMean j t ω}ᶜ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨trajArgmax_spec t ω, fun j hj hjmax ↦ ?_⟩
      exact absurd (trajArgmax_le t ω hjmax) (not_le.mpr hj)
    · rintro ⟨himax, hmin⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hmin _ h (trajArgmax_spec t ω)
      · exact absurd (trajArgmax_le t ω himax) (not_le.mpr h)
  rw [hset]
  refine (hmax i).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ (hmax j).compl)

end Argmax

end BanditAlgorithm

/-!
# The GLR statistic `Z_t` is tie-independent, and measurable

`trajGLR` is written in terms of `trajEmpiricalBestArm`, which is produced by
`Classical.choose` and therefore carries no measurability.  This file shows that
`trajGLR` does not in fact depend on which maximiser is chosen — replacing
`trajEmpiricalBestArm` by the canonical least-index maximiser `trajArgmax` leaves
it unchanged — and concludes that `trajGLR t` is `banditFiltration k t`-measurable.

The mechanism is the same one L&S use in the proof of Lemma 33.7: if the
empirical maximum is attained twice then `Z_t = 0`, because the pair term for two
tied maximisers vanishes.  So the two candidate values of `Z_t` agree: either the
maximiser is unique, and then both formulas use the same arm, or it is not, and
then both formulas return `0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. A generic "measurable finite case split" -/

/-- If `h` is a measurable map into a countable discrete space and each `G a` is
measurable, then so is `ω ↦ G (h ω) ω`. -/
theorem measurable_dep_of_countable {Ω γ ι : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace γ] [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {h : Ω → ι} (hh : Measurable[m] h) {G : ι → Ω → γ} (hG : ∀ a, Measurable[m] (G a)) :
    Measurable[m] fun ω ↦ G (h ω) ω := by
  intro s hs
  have hrw : (fun ω ↦ G (h ω) ω) ⁻¹' s = ⋃ a : ι, (h ⁻¹' {a} ∩ (G a) ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun hω ↦ ⟨h ω, rfl, hω⟩, fun ⟨a, ha, hω⟩ ↦ by rw [← ha] at hω; exact hω⟩
  rw [hrw]
  exact MeasurableSet.iUnion fun a ↦ (hh (measurableSet_singleton a)).inter (hG a hs)

/-! ## 2. Tie-independence -/

section Ties

variable [NeZero k]

/-- The GLR statistic computed at an arbitrary reference arm `a`. -/
noncomputable def trajGLRat (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ≥0∞ :=
  ⨅ j ∈ {j : Fin k | j ≠ a}, ENNReal.ofReal (trajPairGLR a j t ω)

theorem trajGLR_eq_trajGLRat (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR t ω = trajGLRat (trajEmpiricalBestArm t ω) t ω := rfl

/-- The pair term between two arms with equal empirical means vanishes. -/
theorem trajPairGLR_eq_zero_of_mean_eq {a b : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajEmpiricalMean a t ω = trajEmpiricalMean b t ω) :
    trajPairGLR a b t ω = 0 := by
  simp [trajPairGLR, h]

/-- If the empirical maximum is attained at two distinct arms, the GLR statistic
computed at either of them is `0`. -/
theorem trajGLRat_eq_zero_of_tie {a b : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (hab : a ≠ b) (hmean : trajEmpiricalMean a t ω = trajEmpiricalMean b t ω) :
    trajGLRat a t ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_trans (iInf_le_of_le b (iInf_le _ (Ne.symm hab))) (le_of_eq ?_)
  rw [trajPairGLR_eq_zero_of_mean_eq hmean, ENNReal.ofReal_zero]

/-- **Tie-independence.** `Z_t` is unchanged if the arbitrary maximiser produced by
`Classical.choose` is replaced by the canonical least-index maximiser. -/
theorem trajGLR_eq_at_argmax (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR t ω = trajGLRat (trajArgmax t ω) t ω := by
  rw [trajGLR_eq_trajGLRat]
  by_cases h : trajEmpiricalBestArm t ω = trajArgmax t ω
  · rw [h]
  · -- both are maximisers, so their empirical means agree and both sides vanish
    have hmean : trajEmpiricalMean (trajEmpiricalBestArm t ω) t ω
        = trajEmpiricalMean (trajArgmax t ω) t ω :=
      le_antisymm (trajArgmax_spec t ω _) (trajEmpiricalBestArm_spec t ω _)
    rw [trajGLRat_eq_zero_of_tie h hmean, trajGLRat_eq_zero_of_tie (Ne.symm h) hmean.symm]

/-- If the empirical maximum is attained twice, `Z_t = 0`. -/
theorem trajGLR_eq_zero_of_not_unique (t : ℕ) (ω : ℕ → Fin k × ℝ) {b : Fin k}
    (hb : b ≠ trajArgmax t ω) (hmax : ∀ i, trajEmpiricalMean i t ω ≤ trajEmpiricalMean b t ω) :
    trajGLR t ω = 0 := by
  have hmean : trajEmpiricalMean (trajArgmax t ω) t ω = trajEmpiricalMean b t ω :=
    le_antisymm (hmax _) (trajArgmax_spec t ω b)
  rw [trajGLR_eq_at_argmax]
  exact trajGLRat_eq_zero_of_tie (Ne.symm hb) hmean

/-- **Uniqueness from a positive GLR.** If `Z_t ≠ 0` then the empirical maximiser
is unique, so the arbitrary choice made by `trajEmpiricalBestArm` agrees with the
canonical one. -/
theorem trajEmpiricalBestArm_eq_argmax_of_trajGLR_ne_zero (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajGLR t ω ≠ 0) : trajEmpiricalBestArm t ω = trajArgmax t ω := by
  by_contra hne
  exact h (trajGLR_eq_zero_of_not_unique t ω hne (trajEmpiricalBestArm_spec t ω))

/-! ## 3. Measurability of `Z_t` -/

theorem measurable_trajGLRat (a : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajGLRat a t) := by
  have hrw : trajGLRat a t = fun ω ↦ ⨅ j ∈ {j : Fin k | j ≠ a},
      ENNReal.ofReal (trajPairGLR a j t ω) := rfl
  rw [hrw]
  refine Measurable.iInf fun j ↦ ?_
  refine Measurable.iInf fun _ ↦ ?_
  exact ENNReal.measurable_ofReal.comp (measurable_trajPairGLR a j t)

/-- `Z_t` is `𝓕_t`-measurable. -/
theorem measurable_trajGLR (t : ℕ) :
    Measurable[banditFiltration k t] (trajGLR (k := k) t) := by
  have hrw : trajGLR (k := k) t = fun ω ↦ trajGLRat (trajArgmax t ω) t ω := by
    funext ω; exact trajGLR_eq_at_argmax t ω
  rw [hrw]
  exact measurable_dep_of_countable (measurable_trajArgmax t) fun a ↦ measurable_trajGLRat a t

/-- The event "Chernoff's rule fires in round `t`" is `𝓕_t`-measurable. -/
theorem measurableSet_chernoffFires (δ : ℝ) (t : ℕ) :
    MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (chernoffThreshold k δ t) ≤ trajGLR t ω} :=
  measurableSet_le measurable_const (measurable_trajGLR t)

end Ties

end BanditAlgorithm

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
# The Kullback–Leibler divergence between two real Gaussians of equal variance

`D(𝒩(a, v) ‖ 𝒩(b, v)) = (a − b)² / (2v)`.

This is the quantitative input of every fixed-confidence best-arm-identification
bound over the Gaussian class: the characteristic time `c*(ν)` of L&S Eq. (33.4)
is defined through `klDiv`, while the Track-and-Stop statistic `Z_t` is written in
the closed form `½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`, and the two are related
exactly by this identity.  Mathlib computes the mean and the variance of
`gaussianReal` but not its relative entropy.

The proof is the textbook one.  Both measures have a strictly positive density
against Lebesgue measure, so `d𝒩(a,v)/d𝒩(b,v) = pdf_a / pdf_b` Lebesgue-a.e. and
hence `𝒩(a,v)`-a.e., and the log-likelihood ratio collapses to an *affine*
function of `x`:

  `llr x = ((x − b)² − (x − a)²)/(2v) = (a − b)(2x − a − b)/(2v)`.

Only the first moment of a Gaussian is therefore needed, and `∫ x d𝒩(a,v) = a`
gives `(a − b)(2a − a − b)/(2v) = (a − b)²/(2v)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {v : ℝ≥0}

theorem nnreal_coe_pos_of_ne_zero (hv : v ≠ 0) : (0 : ℝ) < (v : ℝ) := by
  have : (0 : ℝ≥0) < v := lt_of_le_of_ne bot_le (Ne.symm hv)
  exact_mod_cast this

/-! ## 1. The logarithm of the Gaussian density -/

theorem log_gaussianPDFReal (hv : v ≠ 0) (m x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = -Real.log (√(2 * π * v)) - (x - m) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hs : (0 : ℝ) < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

/-- The log-likelihood ratio of two Gaussians with the same variance is affine. -/
theorem log_gaussianPDFReal_sub (hv : v ≠ 0) (a b x : ℝ) :
    Real.log (gaussianPDFReal a v x) - Real.log (gaussianPDFReal b v x)
      = (a - b) * (2 * x - a - b) / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  rw [log_gaussianPDFReal hv, log_gaussianPDFReal hv]
  field_simp
  ring

/-! ## 2. The Radon–Nikodym derivative -/

theorem rnDeriv_gaussianReal_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    (gaussianReal a v).rnDeriv (gaussianReal b v)
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * gaussianPDF a v x := by
  have hb : gaussianReal b v = volume.withDensity (gaussianPDF b v) :=
    gaussianReal_of_var_ne_zero _ hv
  have h1 : (gaussianReal a v).rnDeriv (volume.withDensity (gaussianPDF b v))
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * (gaussianReal a v).rnDeriv volume x := by
    refine Measure.rnDeriv_withDensity_right _ _ (measurable_gaussianPDF b v).aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (gaussianPDF_pos b hv x).ne')
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [gaussianPDF]
  have h2 : (gaussianReal a v).rnDeriv volume =ᵐ[volume] gaussianPDF a v :=
    rnDeriv_gaussianReal a v
  rw [hb]
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- The log-likelihood ratio of two same-variance Gaussians, `𝒩(a,v)`-almost
everywhere. -/
theorem llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    llr (gaussianReal a v) (gaussianReal b v)
      =ᵐ[gaussianReal a v] fun x ↦ (a - b) * (2 * x - a - b) / (2 * v) := by
  have hac : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hae : ∀ᵐ x ∂(gaussianReal a v), (gaussianReal a v).rnDeriv (gaussianReal b v) x
      = (gaussianPDF b v x)⁻¹ * gaussianPDF a v x :=
    hac.ae_le (rnDeriv_gaussianReal_gaussianReal hv a b)
  filter_upwards [hae] with x hx
  have hbpos : 0 < gaussianPDFReal b v x := gaussianPDFReal_pos b v x hv
  have hapos : 0 < gaussianPDFReal a v x := gaussianPDFReal_pos a v x hv
  rw [llr, hx, ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_inv_of_pos hbpos, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hapos.le, Real.log_mul (by positivity) hapos.ne', Real.log_inv,
    ← log_gaussianPDFReal_sub hv a b x]
  ring

/-! ## 3. Integrability and the integral -/

/-- `x ↦ x` is integrable against a Gaussian. -/
theorem integrable_id_gaussianReal (m : ℝ) (w : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (gaussianReal m w) := by
  have h : Integrable id (gaussianReal m w) :=
    MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := m) (v := w) 1)
  simpa [Function.id_def] using h

/-- The affine function appearing as the log-likelihood ratio. -/
theorem integrable_llr_form (hv : v ≠ 0) (a b : ℝ) :
    Integrable (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v)) (gaussianReal a v) := by
  have hid := integrable_id_gaussianReal a v
  have h1 : Integrable (fun x : ℝ ↦ 2 * x - a - b) (gaussianReal a v) :=
    (((hid.const_mul 2).sub (integrable_const a)).sub (integrable_const b))
  exact (h1.const_mul (a - b)).div_const (2 * v)

theorem integrable_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) :=
  (integrable_llr_form hv a b).congr (llr_gaussianReal hv a b).symm

theorem integral_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    ∫ x, llr (gaussianReal a v) (gaussianReal b v) x ∂(gaussianReal a v)
      = (a - b) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hid := integrable_id_gaussianReal a v
  rw [integral_congr_ae (llr_gaussianReal hv a b)]
  have hrw : (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v))
      = fun x : ℝ ↦ ((a - b) / (v : ℝ)) * x - (a - b) * (a + b) / (2 * v) := by
    funext x
    field_simp
    ring
  rw [hrw, integral_sub (hid.const_mul _) (integrable_const _), integral_const_mul,
    integral_id_gaussianReal]
  simp only [integral_const, smul_eq_mul, measureReal_univ_eq_one, one_mul]
  field_simp
  ring

/-! ## 4. The divergence -/

/-- **The Kullback–Leibler divergence between two Gaussians of equal variance.** -/
theorem klDiv_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    klDiv (gaussianReal a v) (gaussianReal b v)
      = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  have hac : gaussianReal a v ≪ gaussianReal b v := by
    refine (gaussianReal_absolutelyContinuous a hv).trans ?_
    exact gaussianReal_absolutelyContinuous' b hv
  rw [klDiv_of_ac_of_integrable hac (integrable_llr_gaussianReal hv a b),
    integral_llr_gaussianReal hv a b]
  simp

/-- The unit-variance case, which is the environment class `𝓔^k_𝒩(1)` of L&S
Chapter 33. -/
theorem klDiv_gaussianReal_one (a b : ℝ) :
    klDiv (gaussianReal a 1) (gaussianReal b 1)
      = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  rw [klDiv_gaussianReal one_ne_zero a b]
  norm_num

end BanditAlgorithm

/-!
# The pooled-mean decomposition

The algebraic identity behind the closed form of the Track-and-Stop statistic
`Z_t` (L&S p. 409).  For weights `p, q ≥ 0` with `p + q > 0` and reals `u, v`,

  `p (u − m)² + q (v − m)² = (p + q)(m − m*)² + pq/(p+q) · (u − v)²`,

where `m* = (pu + qv)/(p + q)` is the pooled mean.  Consequently the left-hand
side is minimised at `m = m*`, with minimum value `pq/(p+q) · (u − v)²`.

In the Gaussian bandit this is exactly the statement that

  `inf_{m} [T_a · D(μ̂_a, m) + T_b · D(μ̂_b, m)] = ½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`,

since `D(x, m) = (x − m)²/2` for unit-variance Gaussians: the generalised
likelihood ratio for "arm `a` is not better than arm `b`" collapses to the closed
form used by `trajPairGLR`.
-/

namespace BanditAlgorithm

/-- **Pooled-mean decomposition.** -/
theorem weighted_sq_dist_decomp {p q u v m : ℝ} (hpq : p + q ≠ 0) :
    p * (u - m) ^ 2 + q * (v - m) ^ 2
      = (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 + p * q / (p + q) * (u - v) ^ 2 := by
  field_simp
  ring

/-- The pooled mean minimises the weighted sum of squared distances. -/
theorem pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 ≤ p * (u - m) ^ 2 + q * (v - m) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq.ne']
  have : 0 ≤ (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 :=
    mul_nonneg hpq.le (sq_nonneg _)
  linarith

/-- Equality is attained at the pooled mean. -/
theorem pq_mul_sq_sub_eq {p q u v : ℝ} (hpq : p + q ≠ 0) :
    p * (u - (p * u + q * v) / (p + q)) ^ 2 + q * (v - (p * u + q * v) / (p + q)) ^ 2
      = p * q / (p + q) * (u - v) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq]
  simp

/-- The minimum over `m` of the weighted sum of squared distances is exactly the
pooled term. -/
theorem iInf_weighted_sq_dist {p q u v : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * (u - m) ^ 2 + q * (v - m) ^ 2) = p * q / (p + q) * (u - v) ^ 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * (u - m) ^ 2 + q * (v - m) ^ 2) :=
    ⟨p * q / (p + q) * (u - v) ^ 2, by
      rintro _ ⟨m, rfl⟩
      exact pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ pq_mul_sq_sub_le hp hq hpq)
  exact le_of_le_of_eq (ciInf_le hbdd ((p * u + q * v) / (p + q))) (pq_mul_sq_sub_eq hpq.ne')

/-- Half the pooled term, in the form used by `trajPairGLR`. -/
theorem half_pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * ((u - m) ^ 2 / 2) + q * ((v - m) ^ 2 / 2) := by
  have h := pq_mul_sq_sub_le hp hq hpq (u := u) (v := v) (m := m)
  linarith

end BanditAlgorithm

/-!
# The Gaussian bandit class `𝓔^k_𝒩(1)`, explicitly

Everything the fixed-confidence analysis needs about `gaussianBandit μ`, made
computable:

* `banditArmMean_gaussianBandit` — the arm means are the parameters;
* `banditOptimalMean_gaussianBandit`, `banditOptimalArms_gaussianBandit` — the
  optimal value and the optimal-arm set are the maximum and the argmax of `μ`;
* `klDiv_gaussianBandit` — `D(ν_i ‖ ν'_i) = (μ_i − μ'_i)²/2`;
* `baiAlternatives_gaussianBandit` — membership in `𝓔_alt(ν)` is a condition on
  the parameter vectors only;
* `baiComplexity_inner_gaussianBandit` — the inner sum defining `c*(ν)⁻¹` is
  `∑_i α_i (μ_i − μ'_i)²/2`.

The last three are what turn the abstract characteristic time of L&S Eq. (33.4)
into the quantity Track-and-Stop actually tracks, and `pooled_pair_glr` is the
bridge to the closed form `trajPairGLR` used by `trajGLR`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Means, optimal value, optimal arms -/

@[simp]
theorem banditArmMean_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μvec) i = μvec i := by
  simp [banditArmMean, gaussianBandit, integral_id_gaussianReal]

@[simp]
theorem banditOptimalMean_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalMean (gaussianBandit μvec) = ⨆ i, μvec i := by
  simp [banditOptimalMean]

@[simp]
theorem banditGap_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditGap (gaussianBandit μvec) i = (⨆ j, μvec j) - μvec i := by
  simp [banditGap]

theorem banditOptimalArms_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalArms (gaussianBandit μvec) = {i | μvec i = ⨆ j, μvec j} := by
  ext i
  simp [banditOptimalArms]

/-- With finitely many arms and at least one, the optimal mean is attained. -/
theorem exists_mem_banditOptimalArms [NeZero k] (μvec : Fin k → ℝ) :
    ∃ i, i ∈ banditOptimalArms (gaussianBandit μvec) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k)) μvec
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [banditOptimalArms_gaussianBandit]
  refine le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) ?_
  exact ciSup_le fun j ↦ hi j (Finset.mem_univ j)

/-- An arm is optimal exactly when it maximises the parameter vector. -/
theorem mem_banditOptimalArms_gaussianBandit_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    i ∈ banditOptimalArms (gaussianBandit μvec) ↔ ∀ j, μvec j ≤ μvec i := by
  rw [banditOptimalArms_gaussianBandit]
  constructor
  · intro hi j
    rw [Set.mem_setOf_eq] at hi
    exact hi ▸ le_ciSup (f := μvec) (Finite.bddAbove_range _) j
  · intro hi
    exact le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) (ciSup_le hi)

/-- The gap is positive exactly when the arm is not optimal. -/
theorem banditGap_pos_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    0 < banditGap (gaussianBandit μvec) i ↔ ∃ j, μvec i < μvec j := by
  rw [banditGap_gaussianBandit, sub_pos]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd (ciSup_le hcon) (not_le.mpr h)
  · rintro ⟨j, hj⟩
    exact lt_of_lt_of_le hj (le_ciSup (f := μvec) (Finite.bddAbove_range _) j)

/-! ## 2. Divergences -/

@[simp]
theorem klDiv_gaussianBandit (a b : Fin k → ℝ) (i : Fin k) :
    klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i)
      = ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simpa [gaussianBandit] using klDiv_gaussianReal_one (a i) (b i)

/-- The inner sum in the definition of the characteristic time, for Gaussians. -/
theorem baiComplexity_inner_gaussianBandit (a b : Fin k → ℝ) (α : Fin k → ℝ≥0) :
    (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i))
      = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simp

/-- The alternative set of a Gaussian bandit inside the Gaussian class, in terms
of the parameter vectors. -/
theorem mem_baiAlternatives_gaussianBandit_iff (a : Fin k → ℝ)
    (ν' : StochasticBandit k) :
    ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit a) ↔
      ∃ b : Fin k → ℝ, ν' = gaussianBandit b ∧
        Disjoint (banditOptimalArms (gaussianBandit b))
          (banditOptimalArms (gaussianBandit a)) := by
  constructor
  · rintro ⟨⟨b, rfl⟩, hdisj⟩
    exact ⟨b, rfl, hdisj⟩
  · rintro ⟨b, rfl, hdisj⟩
    exact ⟨⟨b, rfl⟩, hdisj⟩

/-! ## 3. The bridge to the closed-form pair statistic -/

/-- **The Gaussian generalised likelihood ratio for a pair of arms.**  For weights
`p, q ≥ 0` (the pull counts) the least total divergence achievable by moving both
empirical means to a common value `m` is exactly the closed form used by
`trajPairGLR`. -/
theorem pooled_pair_glr {p q u w : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2))
      = p * q / (p + q) * (u - w) ^ 2 / 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2)) :=
    ⟨p * q / (p + q) * (u - w) ^ 2 / 2, by
      rintro _ ⟨m, rfl⟩
      exact half_pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ half_pq_mul_sq_sub_le hp hq hpq)
  refine le_of_le_of_eq (ciInf_le hbdd ((p * u + q * w) / (p + q))) ?_
  have h := pq_mul_sq_sub_eq (p := p) (q := q) (u := u) (v := w) hpq.ne'
  linarith

/-- The pair statistic of `Def_TrackAndStop` is the Gaussian GLR of the pair. -/
theorem trajPairGLR_eq_iInf (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : 0 < (trajPullCount a t ω : ℝ) + (trajPullCount b t ω : ℝ)) :
    trajPairGLR a b t ω
      = ⨅ m : ℝ, ((trajPullCount a t ω : ℝ) * ((trajEmpiricalMean a t ω - m) ^ 2 / 2)
          + (trajPullCount b t ω : ℝ) * ((trajEmpiricalMean b t ω - m) ^ 2 / 2)) := by
  rw [pooled_pair_glr (Nat.cast_nonneg _) (Nat.cast_nonneg _) h]
  rfl

end BanditAlgorithm

/-!
# The characteristic time of a Gaussian bandit, in closed form

For a Gaussian bandit `ν = ν_μ` with a *unique* best arm `i*` and an allocation
`α` with all weights positive, the inner infimum defining `c*(ν)⁻¹` in
L&S Eq. (33.4) is

  `⨅_{ν' ∈ 𝓔_alt(ν)} ∑_i α_i D(ν_i ‖ ν'_i)
      = min_{j ≠ i*} ½ · α_{i*} α_j / (α_{i*} + α_j) · (μ_{i*} − μ_j)²`.

This is *the* formula of the fixed-confidence literature (Garivier–Kaufmann,
COLT 2016, Eq. (3); L&S Eq. (33.4) specialised to `𝓔^k_𝒩(1)`), and it is what
turns the abstract characteristic time into something an algorithm can track.

Both halves come from the pooled-mean decomposition:

* **Lower bound.**  An alternative must make some arm `j ≠ i*` at least as good
  as `i*`, i.e. `μ'_{i*} ≤ μ'_j`.  Writing `a = μ_{i*} − μ'_{i*}` and
  `b = μ'_j − μ_j`, Cauchy–Schwarz gives
  `p a² + q b² ≥ pq/(p+q) (a + b)²`, and `a + b ≥ μ_{i*} − μ_j ≥ 0`.
* **Upper bound.**  Push `μ_{i*}` down to `m − η` and `μ_j` up to `m + η`, where
  `m` is the pooled mean, leaving every other arm alone.  The resulting bandit is
  a legitimate alternative for every `η > 0`, and its cost exceeds the pooled
  value by `2η pq(μ_{i*} − μ_j)/(p+q) + (p+q)η²/2`, which tends to `0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The two real-analytic cores -/

/-- **Lower bound.**  If the alternative reverses the order of the pair, its cost
is at least the pooled value. -/
theorem pooled_le_of_crossed {p q u v x y : ℝ} (hp : 0 < p) (hq : 0 < q)
    (huv : v ≤ u) (hxy : x ≤ y) :
    p * q / (p + q) * (u - v) ^ 2 / 2 ≤ p * ((u - x) ^ 2 / 2) + q * ((v - y) ^ 2 / 2) := by
  have hpq : 0 < p + q := by linarith
  set a : ℝ := u - x with ha
  set b : ℝ := y - v with hb
  have hab : u - v ≤ a + b := by simp only [ha, hb]; linarith
  have huv0 : 0 ≤ u - v := by linarith
  -- Cauchy-Schwarz: `p a² + q b² ≥ pq/(p+q) (a+b)²`
  have hcs : p * q / (p + q) * (a + b) ^ 2 ≤ p * a ^ 2 + q * b ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpq]
    nlinarith [sq_nonneg (q * b - p * a), sq_nonneg (a - b)]
  have hsq : (u - v) ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have hyv : (v - y) ^ 2 = b ^ 2 := by simp only [hb]; ring
  calc p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * q / (p + q) * (a + b) ^ 2 / 2 := by
        have hcoef : 0 ≤ p * q / (p + q) := by positivity
        have := mul_le_mul_of_nonneg_left hsq hcoef
        linarith
    _ ≤ (p * a ^ 2 + q * b ^ 2) / 2 := by linarith
    _ = p * ((u - x) ^ 2 / 2) + q * ((v - y) ^ 2 / 2) := by
        rw [hyv]; simp only [ha]; ring

/-- **Upper bound, exact form.**  Splitting the pair symmetrically around the
pooled mean by `η` costs the pooled value plus an explicit `O(η)` term. -/
theorem cost_of_symmetric_split {p q u v η : ℝ} (hpq : p + q ≠ 0) :
    p * ((u - ((p * u + q * v) / (p + q) - η)) ^ 2 / 2)
        + q * ((v - ((p * u + q * v) / (p + q) + η)) ^ 2 / 2)
      = p * q / (p + q) * (u - v) ^ 2 / 2
        + 2 * η * (p * q * (u - v) / (p + q)) + (p + q) * η ^ 2 / 2 := by
  field_simp
  ring

/-! ## 2. The optimal-arm set of a bandit with a unique best arm -/

theorem banditOptimalArms_eq_singleton [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    banditOptimalArms (gaussianBandit μvec) = {istar} := by
  ext i
  rw [mem_banditOptimalArms_gaussianBandit_iff]
  constructor
  · intro hi
    by_contra hne
    exact absurd (hi istar) (not_le.mpr (hstar i hne))
  · intro hi j
    rw [Set.mem_singleton_iff] at hi
    rw [hi]
    rcases eq_or_ne j istar with rfl | hj
    · exact le_rfl
    · exact (hstar j hj).le

/-- Under a unique best arm, being an alternative just means demoting `i*`. -/
theorem mem_baiAlternatives_iff_of_unique [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) (b : Fin k → ℝ) :
    gaussianBandit b ∈ baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) ↔ ∃ j, b istar < b j := by
  rw [baiAlternatives, Set.mem_setOf_eq, banditOptimalArms_eq_singleton hstar]
  constructor
  · rintro ⟨-, hdisj⟩
    have hnot : istar ∉ banditOptimalArms (gaussianBandit b) := by
      intro hmem
      exact (Set.disjoint_left.mp hdisj hmem) rfl
    rw [mem_banditOptimalArms_gaussianBandit_iff] at hnot
    push_neg at hnot
    obtain ⟨j, hj⟩ := hnot
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨⟨b, rfl⟩, ?_⟩
    rw [Set.disjoint_right]
    rintro i rfl
    rw [mem_banditOptimalArms_gaussianBandit_iff]
    intro hcon
    exact absurd (hcon j) (not_le.mpr hj)

/-! ## 3. The formula -/

/-- The pooled cost of the pair `(i*, j)` under the allocation `α`. -/
noncomputable def pairCost (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k) : ℝ :=
  (α istar : ℝ) * (α j : ℝ) / ((α istar : ℝ) + (α j : ℝ))
    * (μvec istar - μvec j) ^ 2 / 2

/-- **Lower bound half of the closed form.** -/
theorem le_inner_of_alternative [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i) {b : Fin k → ℝ} (hb : ∃ j, b istar < b j) :
    (⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j))
      ≤ ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by
  classical
  obtain ⟨j, hj⟩ := hb
  have hjne : j ≠ istar := by
    rintro rfl
    exact absurd hj (lt_irrefl _)
  have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
  have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
  -- the cost of the two relevant arms already exceeds the pooled value
  have hcore : ENNReal.ofReal (pairCost α μvec istar j)
      ≤ (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
        + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2) := by
    have hreal : pairCost α μvec istar j
        ≤ (α istar : ℝ) * ((μvec istar - b istar) ^ 2 / 2)
          + (α j : ℝ) * ((μvec j - b j) ^ 2 / 2) :=
      pooled_le_of_crossed hp hq (hstar j hjne).le hj.le
    calc ENNReal.ofReal (pairCost α μvec istar j)
        ≤ ENNReal.ofReal ((α istar : ℝ) * ((μvec istar - b istar) ^ 2 / 2)
            + (α j : ℝ) * ((μvec j - b j) ^ 2 / 2)) := ENNReal.ofReal_le_ofReal hreal
      _ = (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
            + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (le_of_lt hp), ENNReal.ofReal_mul (le_of_lt hq),
            ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  refine le_trans (iInf_le_of_le j (iInf_le _ hjne)) (le_trans hcore ?_)
  -- and the full sum is at least the two-term sum
  have hsub : ({istar, j} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  have hpair : (α istar : ℝ≥0∞) * ENNReal.ofReal ((μvec istar - b istar) ^ 2 / 2)
      + (α j : ℝ≥0∞) * ENNReal.ofReal ((μvec j - b j) ^ 2 / 2)
      = ∑ i ∈ ({istar, j} : Finset (Fin k)),
          (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by
    rw [Finset.sum_pair (Ne.symm hjne)]
  rw [hpair]
  exact Finset.sum_le_sum_of_subset hsub

/-! ## 4. Upper bound: the symmetric split is an admissible alternative -/

/-- The alternative that pushes `i*` and `j` symmetrically past each other. -/
noncomputable def splitVec (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k)
    (η : ℝ) : Fin k → ℝ := fun l ↦
  if l = istar then
    ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j) / ((α istar : ℝ) + (α j : ℝ)) - η
  else if l = j then
    ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j) / ((α istar : ℝ) + (α j : ℝ)) + η
  else μvec l

/-- The error incurred by the symmetric split. -/
noncomputable def splitError (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (istar j : Fin k)
    (η : ℝ) : ℝ :=
  2 * η * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j) / ((α istar : ℝ) + (α j : ℝ)))
    + ((α istar : ℝ) + (α j : ℝ)) * η ^ 2 / 2

theorem splitError_nonneg {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k} {η : ℝ}
    (hη : 0 ≤ η) (huv : μvec j ≤ μvec istar) : 0 ≤ splitError α μvec istar j η := by
  unfold splitError
  have h1 : 0 ≤ (α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ μvec istar - μvec j := by linarith
    positivity
  have h2 : 0 ≤ ((α istar : ℝ) + (α j : ℝ)) * η ^ 2 / 2 := by positivity
  have h3 : 0 ≤ 2 * η * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ))) := by positivity
  linarith

theorem splitError_le {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) (huv : μvec j ≤ μvec istar) :
    splitError α μvec istar j η
      ≤ η * (2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
          / ((α istar : ℝ) + (α j : ℝ))) + ((α istar : ℝ) + (α j : ℝ)) / 2) := by
  unfold splitError
  have hC : 0 ≤ (α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ μvec istar - μvec j := by linarith
    positivity
  have hsq : η ^ 2 ≤ η := by nlinarith
  have hpq : (0 : ℝ) ≤ (α istar : ℝ) + (α j : ℝ) := by positivity
  nlinarith

/-- The cost of the split alternative, exactly. -/
theorem sum_cost_splitVec {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} {istar j : Fin k}
    (hj : j ≠ istar) (hα : ∀ i, 0 < α i) (η : ℝ) (hη : 0 ≤ η)
    (huv : μvec j ≤ μvec istar) :
    (∑ i, (α i : ℝ≥0∞) *
        ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2))
      = ENNReal.ofReal (pairCost α μvec istar j + splitError α μvec istar j η) := by
  classical
  have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
  have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
  have hpq : (α istar : ℝ) + (α j : ℝ) ≠ 0 := by positivity
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      i ∉ ({istar, j} : Finset (Fin k)) →
      (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp [splitVec, hi.1, hi.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({istar, j} : Finset (Fin k))) hzero,
    Finset.sum_pair (Ne.symm hj)]
  have hi1 : splitVec α μvec istar j η istar
      = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
          / ((α istar : ℝ) + (α j : ℝ)) - η := by simp [splitVec]
  have hi2 : splitVec α μvec istar j η j
      = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
          / ((α istar : ℝ) + (α j : ℝ)) + η := by simp [splitVec, hj]
  rw [hi1, hi2]
  set m : ℝ := ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
      / ((α istar : ℝ) + (α j : ℝ)) with hm
  set A : ℝ := (μvec istar - (m - η)) ^ 2 / 2 with hA
  set B : ℝ := (μvec j - (m + η)) ^ 2 / 2 with hB
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hlhs : (α istar : ℝ≥0∞) * ENNReal.ofReal A + (α j : ℝ≥0∞) * ENNReal.ofReal B
      = ENNReal.ofReal ((α istar : ℝ) * A + (α j : ℝ) * B) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hp.le, ENNReal.ofReal_mul hq.le,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [hlhs]
  congr 1
  have hsplit := cost_of_symmetric_split (p := (α istar : ℝ)) (q := (α j : ℝ))
    (u := μvec istar) (v := μvec j) (η := η) hpq
  rw [hA, hB, hm, hsplit]
  unfold pairCost splitError
  ring

theorem pairCost_nonneg {α : Fin k → ℝ≥0} {μvec : Fin k → ℝ} (istar j : Fin k) :
    0 ≤ pairCost α μvec istar j := by
  unfold pairCost
  positivity

/-! ## 5. The closed form -/

/-- **The characteristic-time formula for a Gaussian bandit.**  For an allocation
with strictly positive weights and a bandit with a unique best arm, the inner
infimum of L&S Eq. (33.4) is the minimum over the competing arms of the pooled
pair cost. -/
theorem inner_gaussian_eq [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0} (hα : ∀ i, 0 < α i) :
    (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
      = ⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j) := by
  classical
  refine le_antisymm ?_ ?_
  · -- every competing arm gives an admissible alternative, up to `η`
    refine le_iInf₂ fun j hj ↦ ?_
    have hjne : j ≠ istar := hj
    have hp : (0 : ℝ) < (α istar : ℝ) := by exact_mod_cast hα istar
    have hq : (0 : ℝ) < (α j : ℝ) := by exact_mod_cast hα j
    set C : ℝ := 2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
        / ((α istar : ℝ) + (α j : ℝ))) + ((α istar : ℝ) + (α j : ℝ)) / 2 with hCdef
    have hC : 0 < C := by
      have h1 : 0 ≤ 2 * ((α istar : ℝ) * (α j : ℝ) * (μvec istar - μvec j)
          / ((α istar : ℝ) + (α j : ℝ))) := by
        have : 0 ≤ μvec istar - μvec j := by linarith [hstar j hjne]
        apply mul_nonneg (by norm_num)
        apply div_nonneg _ (by positivity)
        positivity
      have h2 : 0 < ((α istar : ℝ) + (α j : ℝ)) / 2 := by positivity
      rw [hCdef]; linarith
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    set η : ℝ := min 1 ((ε : ℝ) / C) with hηdef
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    have hη0 : 0 < η := lt_min one_pos (div_pos hεR hC)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hserr : splitError α μvec istar j η ≤ (ε : ℝ) := by
      calc splitError α μvec istar j η ≤ η * C :=
            splitError_le hη0 hη1 (hstar j hjne).le
        _ ≤ ((ε : ℝ) / C) * C := by
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hC.le
        _ = (ε : ℝ) := by field_simp
    have hmem : gaussianBandit (splitVec α μvec istar j η)
        ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec) := by
      rw [mem_baiAlternatives_iff_of_unique hstar]
      refine ⟨j, ?_⟩
      have h1 : splitVec α μvec istar j η istar
          = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
              / ((α istar : ℝ) + (α j : ℝ)) - η := by simp [splitVec]
      have h2 : splitVec α μvec istar j η j
          = ((α istar : ℝ) * μvec istar + (α j : ℝ) * μvec j)
              / ((α istar : ℝ) + (α j : ℝ)) + η := by simp [splitVec, hjne]
      rw [h1, h2]; linarith
    calc (⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
        ≤ ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i)
            ((gaussianBandit (splitVec α μvec istar j η)).P i) :=
          iInf₂_le _ hmem
      _ = ∑ i, (α i : ℝ≥0∞) *
            ENNReal.ofReal ((μvec i - splitVec α μvec istar j η i) ^ 2 / 2) := by
          simp
      _ = ENNReal.ofReal (pairCost α μvec istar j + splitError α μvec istar j η) :=
          sum_cost_splitVec hjne hα η hη0.le (hstar j hjne).le
      _ = ENNReal.ofReal (pairCost α μvec istar j)
            + ENNReal.ofReal (splitError α μvec istar j η) :=
          ENNReal.ofReal_add (pairCost_nonneg _ _)
            (splitError_nonneg hη0.le (hstar j hjne).le)
      _ ≤ ENNReal.ofReal (pairCost α μvec istar j) + (ε : ℝ≥0∞) := by
          gcongr
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal hserr
  · -- every alternative costs at least the pooled minimum
    refine le_iInf₂ fun ν' hν' ↦ ?_
    obtain ⟨b, rfl⟩ : ∃ b : Fin k → ℝ, gaussianBandit b = ν' := hν'.1
    have hb : ∃ l, b istar < b l := (mem_baiAlternatives_iff_of_unique hstar b).mp hν'
    have hrw : (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i)
        ((gaussianBandit b).P i))
        = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((μvec i - b i) ^ 2 / 2) := by simp
    rw [hrw]
    exact le_inner_of_alternative hstar hα hb

end BanditAlgorithm

/-!
# The GLR statistic grows linearly once the empirical quantities have settled

This is the deterministic half of Garivier & Kaufmann's Theorem 14.  Chernoff's
statistic is

  `Z_t = min_{j ≠ î(t)}  ½ · T_î T_j/(T_î + T_j) · (μ̂_î − μ̂_j)²`,

and `T_i(t) = t · w_i(t)` where `w(t)` is the empirical allocation.  Factoring `t`
out of `T_î T_j/(T_î + T_j)` gives exactly

  `Z_t = t · min_{j ≠ î(t)} pairCost(w(t), μ̂(t))`,                        (∗)

with `pairCost` the very function whose maximum over the simplex defines
`c*(ν)⁻¹` (`Solutions/GaussianComplexity.lean`).  So the moment the empirical
allocation is near `α*` and the empirical means are near `μ`, the statistic is
near `t/c*(ν)` — a line of slope `1/c*(ν)`.

What is proved here is the one-sided, quantitative version of that: if

  `|w_i − α_i| ≤ ξ` and `|μ̂_i − μ_i| ≤ ξ` for every `i`,

then the empirical best arm is the true one and

  `Z_t ≥ t · min_{j ≠ i*} (α_{i*} − ξ)(α_j − ξ)/((α_{i*} − ξ) + (α_j − ξ)) ·
                          ((μ_{i*} − μ_j) − 2ξ)²/2`.

The right-hand side is a continuous function of `ξ` equal to `t/c*(ν)` at `ξ = 0`,
so for every slope `r < 1/c*(ν)` there is a `ξ > 0` for which it exceeds `r t`.
That is the "eventually above a line of slope `r`" hypothesis consumed by
`Solutions/StoppingBridge.lean`.

Nothing probabilistic happens in this file: it is an inequality about a single
trajectory at a single round.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The pair rate as a function of allocation and means -/

/-- The real-valued pair cost: `pairCost` with an unrestricted (not necessarily
`ℝ≥0`-valued) allocation, which is what the *empirical* allocation is. -/
noncomputable def pairRate (w m : Fin k → ℝ) (a b : Fin k) : ℝ :=
  w a * w b / (w a + w b) * (m a - m b) ^ 2 / 2

theorem pairRate_eq_pairCost (α : Fin k → ℝ≥0) (μvec : Fin k → ℝ) (a b : Fin k) :
    pairRate (fun i ↦ (α i : ℝ)) μvec a b = pairCost α μvec a b := rfl

/-- **The scaling identity (∗).**  `T_a T_b/(T_a + T_b) (μ̂_a − μ̂_b)²/2
= t · pairRate(w, μ̂)`. -/
theorem trajPairGLR_eq_mul_pairRate (a b : Fin k) {t : ℕ} (ht : 0 < t)
    (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a b t ω
      = (t : ℝ) * pairRate (fun i ↦ trajAllocation i t ω)
          (fun i ↦ trajEmpiricalMean i t ω) a b := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  simp only [trajPairGLR, pairRate, trajAllocation_eq]
  set A : ℝ := (trajPullCount a t ω : ℝ) with hA
  set B : ℝ := (trajPullCount b t ω : ℝ) with hB
  rcases eq_or_ne (A + B) 0 with hAB | hAB
  · -- both counts vanish: every term is `0`
    have hA0 : A = 0 := by
      have hA0' : 0 ≤ A := Nat.cast_nonneg _
      have hB0' : 0 ≤ B := Nat.cast_nonneg _
      linarith
    have hB0 : B = 0 := by
      have hA0' : 0 ≤ A := Nat.cast_nonneg _
      have hB0' : 0 ≤ B := Nat.cast_nonneg _
      linarith
    rw [hA0, hB0]
    simp
  · have hsum : A / (t : ℝ) + B / (t : ℝ) = (A + B) / (t : ℝ) := by ring
    rw [hsum]
    field_simp

/-! ## Monotonicity of the harmonic factor -/

/-- `x y/(x + y)` is monotone in each argument on the positives: this is the
statement `1/(1/x + 1/y)` is monotone, written without division by `x` or `y`. -/
theorem pairFrac_mono {p q x y : ℝ} (hp : 0 < p) (hq : 0 < q) (hpx : p ≤ x)
    (hqy : q ≤ y) : p * q / (p + q) ≤ x * y / (x + y) := by
  have hx : 0 < x := lt_of_lt_of_le hp hpx
  have hy : 0 < y := lt_of_lt_of_le hq hqy
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  -- `p q (x + y) ≤ x y (p + q)` ⟺ `p x (y − q) + q y (x − p) ≥ 0`
  nlinarith [mul_nonneg (mul_nonneg hp.le hx.le) (sub_nonneg.mpr hqy),
    mul_nonneg (mul_nonneg hq.le hy.le) (sub_nonneg.mpr hpx)]

theorem pairFrac_nonneg' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x * y / (x + y) := by positivity

/-! ## The lower bound at a single pair -/

/-- The pair rate under `ξ`-perturbation of the allocation and the means. -/
noncomputable def pairRateLower (α : Fin k → ℝ) (μvec : Fin k → ℝ) (ξ : ℝ)
    (a b : Fin k) : ℝ :=
  (α a - ξ) * (α b - ξ) / ((α a - ξ) + (α b - ξ))
    * ((μvec a - μvec b) - 2 * ξ) ^ 2 / 2

/-- **Continuity of the pair rate in the perturbation size**, one-sided.  If the
empirical allocation and means are within `ξ` of `(α, μ)` and `ξ` is smaller than
both weights and than half the gap, the pair rate is at least
`pairRateLower α μ ξ`. -/
theorem pairRate_ge_of_close {w m α μvec : Fin k → ℝ} {a b : Fin k} {ξ : ℝ}
    (hξ : 0 ≤ ξ) (hw : ∀ i, |w i - α i| ≤ ξ) (hm : ∀ i, |m i - μvec i| ≤ ξ)
    (hpa : ξ < α a) (hpb : ξ < α b) (hgap : 2 * ξ ≤ μvec a - μvec b) :
    pairRateLower α μvec ξ a b ≤ pairRate w m a b := by
  have hwa : α a - ξ ≤ w a := by
    have := abs_le.mp (hw a); linarith [this.1]
  have hwb : α b - ξ ≤ w b := by
    have := abs_le.mp (hw b); linarith [this.1]
  have hpa' : 0 < α a - ξ := by linarith
  have hpb' : 0 < α b - ξ := by linarith
  -- the harmonic factor
  have hfrac : (α a - ξ) * (α b - ξ) / ((α a - ξ) + (α b - ξ))
      ≤ w a * w b / (w a + w b) := pairFrac_mono hpa' hpb' hwa hwb
  -- the squared gap
  have hma : μvec a - ξ ≤ m a := by
    have := abs_le.mp (hm a); linarith [this.1]
  have hmb : m b ≤ μvec b + ξ := by
    have := abs_le.mp (hm b); linarith [this.2]
  have hd0 : 0 ≤ (μvec a - μvec b) - 2 * ξ := by linarith
  have hdiff : (μvec a - μvec b) - 2 * ξ ≤ m a - m b := by linarith
  have hsq : ((μvec a - μvec b) - 2 * ξ) ^ 2 ≤ (m a - m b) ^ 2 := by
    nlinarith
  have hfnn : (0 : ℝ) ≤ (α a - ξ) * (α b - ξ) / ((α a - ξ) + (α b - ξ)) := by
    positivity
  rw [pairRateLower, pairRate]
  have hstep : (α a - ξ) * (α b - ξ) / ((α a - ξ) + (α b - ξ))
      * ((μvec a - μvec b) - 2 * ξ) ^ 2
      ≤ w a * w b / (w a + w b) * (m a - m b) ^ 2 := by
    refine le_trans (mul_le_mul_of_nonneg_left hsq hfnn) ?_
    exact mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
  linarith

/-- At `ξ = 0` the lower bound is the pair cost itself. -/
theorem pairRateLower_zero (α μvec : Fin k → ℝ) (a b : Fin k) :
    pairRateLower α μvec 0 a b = pairRate α μvec a b := by
  simp [pairRateLower, pairRate]

/-- The lower bound is continuous in `ξ` at `0` when both weights are positive. -/
theorem continuousAt_pairRateLower {α μvec : Fin k → ℝ} {a b : Fin k}
    (hpa : 0 < α a) (hpb : 0 < α b) :
    ContinuousAt (fun ξ : ℝ ↦ pairRateLower α μvec ξ a b) 0 := by
  have hden : (α a - (0:ℝ)) + (α b - (0:ℝ)) ≠ 0 := by
    simp only [sub_zero]; positivity
  simp only [pairRateLower]
  refine ContinuousAt.div_const (ContinuousAt.mul ?_ ?_) 2
  · refine ContinuousAt.div ?_ ?_ hden
    · exact ((continuous_const.sub continuous_id).mul
        (continuous_const.sub continuous_id)).continuousAt
    · exact ((continuous_const.sub continuous_id).add
        (continuous_const.sub continuous_id)).continuousAt
  · exact (((continuous_const.sub (continuous_const.mul continuous_id))).pow 2).continuousAt

/-! ## The empirical best arm is the true one -/

variable [NeZero k]

/-- If the empirical means are within `ξ` of the true ones and the smallest gap
exceeds `2ξ`, the empirical maximiser is the true best arm. -/
theorem trajEmpiricalBestArm_eq_of_close {μvec : Fin k → ℝ} {istar : Fin k}
    {t : ℕ} {ω : ℕ → Fin k × ℝ} {ξ : ℝ}
    (hm : ∀ i, |trajEmpiricalMean i t ω - μvec i| ≤ ξ)
    (hgap : ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j) :
    trajEmpiricalBestArm t ω = istar := by
  by_contra hne
  have hle := trajEmpiricalBestArm_spec t ω istar
  set b : Fin k := trajEmpiricalBestArm t ω with hb
  have hgapb : 2 * ξ < μvec istar - μvec b := hgap b hne
  have h1 : μvec istar - ξ ≤ trajEmpiricalMean istar t ω := by
    have := abs_le.mp (hm istar); linarith [this.1]
  have h2 : trajEmpiricalMean b t ω ≤ μvec b + ξ := by
    have := abs_le.mp (hm b); linarith [this.2]
  linarith

/-! ## The statistic is above a line -/

/-- **The linear lower bound on `Z_t`.**  Under `ξ`-closeness of the empirical
allocation and means, `Z_t ≥ t · min_{j ≠ i*} pairRateLower`. -/
theorem trajGLR_ge_of_close {μvec : Fin k → ℝ} {istar : Fin k} {α : Fin k → ℝ}
    {t : ℕ} (ht : 0 < t) {ω : ℕ → Fin k × ℝ} {ξ ρ : ℝ} (hξ : 0 ≤ ξ)
    (hw : ∀ i, |trajAllocation i t ω - α i| ≤ ξ)
    (hm : ∀ i, |trajEmpiricalMean i t ω - μvec i| ≤ ξ)
    (hpos : ∀ i, ξ < α i)
    (hgap : ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j)
    (hρ : ∀ j, j ≠ istar → ρ ≤ pairRateLower α μvec ξ istar j) :
    ENNReal.ofReal ((t : ℝ) * ρ) ≤ trajGLR t ω := by
  have hbest : trajEmpiricalBestArm t ω = istar :=
    trajEmpiricalBestArm_eq_of_close hm hgap
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  rw [trajGLR]
  refine le_iInf₂ fun j hj ↦ ?_
  have hjne : j ≠ istar := by rw [hbest] at hj; exact hj
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hbest]
  have hkey : ρ ≤ pairRate (fun i ↦ trajAllocation i t ω)
      (fun i ↦ trajEmpiricalMean i t ω) istar j :=
    le_trans (hρ j hjne)
      (pairRate_ge_of_close hξ hw hm (hpos istar) (hpos j) (hgap j hjne).le)
  calc (t : ℝ) * ρ ≤ (t : ℝ) * pairRate (fun i ↦ trajAllocation i t ω)
        (fun i ↦ trajEmpiricalMean i t ω) istar j := by
        exact mul_le_mul_of_nonneg_left hkey htR.le
    _ = trajPairGLR istar j t ω := (trajPairGLR_eq_mul_pairRate istar j ht ω).symm

end BanditAlgorithm

/-!
# From tracking convergence to "the statistic is eventually above a line"

`Solutions/GLRRate.lean` bounds `Z_t` from below at a *single* round, given that
the empirical allocation and means are within `ξ` of `(α, μ)`.  This file turns
that into the asymptotic statement the stopping-time bound consumes:

> If `w_i(t) → α_i` and `μ̂_i(t) → μ_i` along a trajectory, then for every slope
> `r` strictly below the pair rate `min_{j ≠ i*} pairRate(α, μ)`, there is a
> round `N(ω)` from which `Z_t ≥ r t`.

The only content is a two-stage choice of `ξ`.  First `ξ` is chosen small enough
that the *deterministic* lower bound `pairRateLower(α, μ, ξ)` still exceeds `r`;
this is possible because `pairRateLower` is continuous in `ξ` with value
`pairRate` at `ξ = 0`, and there are finitely many competing arms, so finitely
many conditions to satisfy at once.  Then the convergence hypotheses put the
trajectory inside the `ξ`-window from some round on.

The slope `r` can be taken as close to `min_{j ≠ i*} pairRate(α*, μ) = 1/c*(ν)`
as one likes, which is what makes the leading constant of Theorem 33.6 come out
to `c*(ν)` rather than something larger.  It cannot be taken *equal* to
`1/c*(ν)`: at `ξ = 0` the window is empty.  That is the origin of the `ε` in the
statement of `chernoff_stopping_time_le_integrable_plus_linear`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Topology

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## Choosing the window `ξ` -/

/-- The finitely many conditions on `ξ` hold simultaneously for all small `ξ > 0`:
`ξ` below every weight, `2ξ` below every gap, and the perturbed rate still above
`r`. -/
theorem exists_window {μvec α : Fin k → ℝ} {istar : Fin k} {r : ℝ}
    (hα : ∀ i, 0 < α i) (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hr : ∀ j, j ≠ istar → r < pairRate α μvec istar j) :
    ∃ ξ : ℝ, 0 < ξ ∧ (∀ i, ξ < α i) ∧ (∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j) ∧
      ∀ j, j ≠ istar → r ≤ pairRateLower α μvec ξ istar j := by
  classical
  -- (a) `ξ < α i` for every `i`
  have hA : ∀ᶠ ξ : ℝ in 𝓝 (0 : ℝ), ∀ i, ξ < α i := by
    rw [Filter.eventually_all]
    intro i
    exact gt_mem_nhds (hα i)
  -- (b) `2ξ` below every gap
  have hB : ∀ᶠ ξ : ℝ in 𝓝 (0 : ℝ), ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = istar
    · exact Eventually.of_forall fun _ h ↦ absurd hj h
    · have hgap : (0 : ℝ) < μvec istar - μvec j := by
        have := hstar j hj; linarith
      have htend : Tendsto (fun ξ : ℝ ↦ 2 * ξ) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
        simpa using (tendsto_id (α := ℝ) (x := 𝓝 (0:ℝ))).const_mul 2
      have : ∀ᶠ ξ : ℝ in 𝓝 (0 : ℝ), 2 * ξ < μvec istar - μvec j :=
        htend.eventually (gt_mem_nhds hgap)
      exact this.mono fun ξ h _ ↦ h
  -- (c) the perturbed rate is still above `r`
  have hC : ∀ᶠ ξ : ℝ in 𝓝 (0 : ℝ), ∀ j, j ≠ istar → r ≤ pairRateLower α μvec ξ istar j := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = istar
    · exact Eventually.of_forall fun _ h ↦ absurd hj h
    · have hcont : ContinuousAt (fun ξ : ℝ ↦ pairRateLower α μvec ξ istar j) 0 :=
        continuousAt_pairRateLower (hα istar) (hα j)
      have hval : (fun ξ : ℝ ↦ pairRateLower α μvec ξ istar j) 0
          = pairRate α μvec istar j := pairRateLower_zero α μvec istar j
      have htend : Tendsto (fun ξ : ℝ ↦ pairRateLower α μvec ξ istar j) (𝓝 0)
          (𝓝 (pairRate α μvec istar j)) := by
        rw [← hval]; exact hcont
      have : ∀ᶠ ξ : ℝ in 𝓝 (0 : ℝ), r < pairRateLower α μvec ξ istar j :=
        htend.eventually (eventually_gt_nhds (hr j hj))
      exact this.mono fun ξ h _ ↦ h.le
  -- put the three together and pick a positive `ξ`
  have hpos : ∀ᶠ ξ : ℝ in 𝓝[>] (0 : ℝ), 0 < ξ := self_mem_nhdsWithin
  have hall := ((hA.and (hB.and hC)).filter_mono nhdsWithin_le_nhds).and hpos
  obtain ⟨ξ, ⟨hξA, hξB, hξC⟩, hξ0⟩ := hall.exists
  exact ⟨ξ, hξ0, hξA, hξB, hξC⟩

/-! ## The asymptotic lower bound -/

/-- **The statistic is eventually above every line of slope below the pair
rate.**  This is the hypothesis consumed by
`chernoffStoppingTime_le_crossWitness_add`. -/
theorem exists_eventually_glr_ge_line {μvec α : Fin k → ℝ} {istar : Fin k} {r : ℝ}
    (hα : ∀ i, 0 < α i) (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hr : ∀ j, j ≠ istar → r < pairRate α μvec istar j)
    {ω : ℕ → Fin k × ℝ}
    (hwlim : ∀ i, Tendsto (fun t : ℕ ↦ trajAllocation i t ω) atTop (𝓝 (α i)))
    (hmlim : ∀ i, Tendsto (fun t : ℕ ↦ trajEmpiricalMean i t ω) atTop (𝓝 (μvec i))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω := by
  classical
  obtain ⟨ξ, hξ0, hξα, hξgap, hξrate⟩ := exists_window hα hstar hr
  -- the trajectory enters the `ξ`-window
  have hwin : ∀ᶠ t : ℕ in atTop,
      (∀ i, |trajAllocation i t ω - α i| ≤ ξ) ∧
        (∀ i, |trajEmpiricalMean i t ω - μvec i| ≤ ξ) := by
    have hw : ∀ᶠ t : ℕ in atTop, ∀ i, |trajAllocation i t ω - α i| ≤ ξ := by
      rw [Filter.eventually_all]
      intro i
      have := (Metric.tendsto_nhds.mp (hwlim i)) ξ hξ0
      exact this.mono fun t ht ↦ le_of_lt (by rwa [Real.dist_eq] at ht)
    have hm : ∀ᶠ t : ℕ in atTop, ∀ i, |trajEmpiricalMean i t ω - μvec i| ≤ ξ := by
      rw [Filter.eventually_all]
      intro i
      have := (Metric.tendsto_nhds.mp (hmlim i)) ξ hξ0
      exact this.mono fun t ht ↦ le_of_lt (by rwa [Real.dist_eq] at ht)
    exact hw.and hm
  obtain ⟨N, hN⟩ := (hwin.and (eventually_gt_atTop 0)).exists_forall_of_atTop
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨⟨hw, hm⟩, hn0⟩ := hN n hn
  have h := trajGLR_ge_of_close hn0 hξ0.le hw hm hξα hξgap hξrate
  rwa [mul_comm (r : ℝ) ((n : ℕ) : ℝ)]

end BanditAlgorithm

/-!
# Chernoff's stopping rule: threshold arithmetic and the stopping-time property

This file establishes the two *structural* clauses of L&S Lemma 33.7 — everything
about `τ_δ` and `ψ_δ` except the probability bound itself:

* `chernoffInverse_ge`, `chernoffThreshold_pos` — the threshold `β_t(δ)` is
  strictly positive.  This is what forces the empirical maximiser to be unique
  whenever the learner stops, which is in turn what makes the recommendation
  measurable at all (`chernoffRecommendation` is built from the `Classical.choose`
  maximiser `trajEmpiricalBestArm`).
* `isBanditStoppingTime_chernoffStoppingTime` — `τ_δ` is a stopping time of the
  natural filtration.
* `measurable_chernoffRecommendation` — `ψ_δ` is `𝓕_{τ_δ}`-measurable.

The positivity argument is the one implicit in L&S p. 410: `f⁻¹(δ)` is the least
`x ≥ k` with `f(x) ≤ δ`, so `f⁻¹(δ) ≥ k ≥ 1` as soon as that set is nonempty —
which it is, because `f(x) = e^{k-x}(x/k)^k → 0` as `x → ∞`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The Chernoff function and its inverse -/

/-- `f(k) = 1`. -/
theorem chernoffF_self (hk : 0 < k) : chernoffF k (k : ℝ) = 1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [chernoffF, div_self hk']

/-- `f(x) = e^{k-x}(x/k)^k` tends to `0` as `x → ∞`. -/
theorem tendsto_chernoffF (hk : 0 < k) :
    Tendsto (chernoffF k) atTop (nhds 0) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hrw : chernoffF k = fun x : ℝ ↦
      (Real.exp (k : ℝ) / ((k : ℝ) ^ k)) * (x ^ k * Real.exp (-x)) := by
    funext x
    rw [chernoffF, div_pow, sub_eq_add_neg, Real.exp_add]
    field_simp
  rw [hrw]
  simpa using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero k)

/-- The set defining `f⁻¹(δ)` is nonempty for every `δ > 0`. -/
theorem chernoffInverse_set_nonempty (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}.Nonempty := by
  have h1 : ∀ᶠ x : ℝ in atTop, chernoffF k x ≤ δ :=
    (tendsto_chernoffF hk).eventually (eventually_le_nhds hδ)
  have h2 : ∀ᶠ x : ℝ in atTop, (k : ℝ) ≤ x := eventually_ge_atTop _
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  exact ⟨x, hx2, hx1⟩

theorem chernoffInverse_set_bddBelow {δ : ℝ} :
    BddBelow {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  ⟨(k : ℝ), fun _ hx ↦ hx.1⟩

/-- `f⁻¹(δ) ≥ k`. -/
theorem chernoffInverse_ge (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ :=
  le_csInf (chernoffInverse_set_nonempty hk hδ) fun _ hx ↦ hx.1

/-- `f⁻¹(δ) > 0`. -/
theorem chernoffInverse_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (chernoffInverse_ge hk hδ)

/-- The threshold `β_t(δ) = k log(t² + t) + f⁻¹(δ)` is strictly positive. -/
theorem chernoffThreshold_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    0 < chernoffThreshold k δ t := by
  have hlog : 0 ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ)) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · norm_num
    · refine mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg ?_)
      have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      nlinarith
  have hinv := chernoffInverse_pos hk hδ
  rw [chernoffThreshold]
  linarith

/-! ## 2. The stopping-time property -/

section Stop

variable [NeZero k]

/-- Unfolding of the stopping rule: the learner has stopped by round `n` exactly
when the firing condition has held at some round `m ≤ n`. -/
theorem chernoffStoppingTime_le_iff (δ : ℝ) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    chernoffStoppingTime (k := k) δ ω ≤ (n : ℕ∞) ↔
      ∃ m ≤ n, ENNReal.ofReal (chernoffThreshold k δ m) ≤ trajGLR m ω := by
  constructor
  · intro hle
    by_contra hcon
    push_neg at hcon
    -- every element of the defining set exceeds `n`, hence is `≥ n + 1`
    have hlb : ((n : ℕ∞) + 1) ≤ chernoffStoppingTime (k := k) δ ω := by
      refine le_sInf ?_
      rintro t ⟨m, rfl, hm⟩
      have hmn : n < m := by
        by_contra h
        exact absurd hm (not_le.mpr (hcon m (not_lt.mp h)))
      have : ((n + 1 : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.succ_le_of_lt hmn
      simpa using this
    have hcontr : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      push_cast
      exact le_trans hlb hle
    exact absurd (by exact_mod_cast hcontr : n + 1 ≤ n) (Nat.not_succ_le_self n)
  · rintro ⟨m, hmn, hm⟩
    refine le_trans (sInf_le ⟨m, rfl, hm⟩) ?_
    exact_mod_cast hmn

/-- **Chernoff's rule is a stopping time.** -/
theorem isBanditStoppingTime_chernoffStoppingTime (δ : ℝ) :
    IsBanditStoppingTime (chernoffStoppingTime (k := k) δ) := by
  intro n
  show MeasurableSet[banditFiltration k n]
    {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)}
  have hrw : {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)} =
      ⋃ m ∈ Finset.range (n + 1),
        {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (chernoffThreshold k δ m) ≤ trajGLR m ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
    exact chernoffStoppingTime_le_iff δ n ω
  rw [hrw]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (banditFiltration k).mono hmn _ (measurableSet_chernoffFires δ m)

/-- `{τ_δ = m}` is `𝓕_m`-measurable. -/
theorem measurableSet_chernoffStoppingTime_eq (δ : ℝ) (m : ℕ) :
    MeasurableSet[banditFiltration k m]
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} := by
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  have hset : {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} =
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((m : ℕ) : ℕ∞)} \
        ⋃ l ∈ Finset.range m,
          {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((l : ℕ) : ℕ∞)} := by
    ext ω
    simp only [Set.mem_diff, Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq,
      exists_prop, not_exists, not_and]
    constructor
    · rintro h
      refine ⟨le_of_eq h, fun l hl hle ↦ ?_⟩
      rw [h] at hle
      exact absurd (by exact_mod_cast hle : m ≤ l) (not_le.mpr hl)
    · rintro ⟨hle, hlt⟩
      rcases lt_or_eq_of_le hle with h | h
      · exfalso
        obtain ⟨l, hl⟩ : ∃ l : ℕ, ((l : ℕ) : ℕ∞) = chernoffStoppingTime (k := k) δ ω :=
          ENat.ne_top_iff_exists.mp fun htop ↦ by
            rw [htop] at hle; exact absurd hle (by simp)
        rw [← hl] at h
        exact hlt l (by exact_mod_cast h) (le_of_eq hl.symm)
      · exact h
  rw [hset]
  refine MeasurableSet.diff (hτ m) ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun l hl ↦ ?_
  exact (banditFiltration k).mono (le_of_lt (Finset.mem_range.mp hl)) _ (hτ l)

/-- `τ_δ` is measurable for the ambient σ-algebra. -/
theorem measurable_chernoffStoppingTime (δ : ℝ) :
    Measurable (chernoffStoppingTime (k := k) δ) := by
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  refine @measurable_to_countable' ℕ∞ _ _ _ _ _ fun c ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · have hrw : (chernoffStoppingTime (k := k) δ) ⁻¹' {(⊤ : ℕ∞)} =
        (⋃ n : ℕ, {ω : ℕ → Fin k × ℝ |
          chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact ENat.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
        rw [← hn] at h
        exact absurd (h n) (lt_irrefl _)
    rw [hrw]
    exact (MeasurableSet.iUnion fun n ↦ (banditFiltration k).le n _ (hτ n)).compl
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hc
    have hrw : (chernoffStoppingTime (k := k) δ) ⁻¹' {((m : ℕ) : ℕ∞)} =
        {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} := rfl
    rw [hrw]
    exact (banditFiltration k).le m _ (measurableSet_chernoffStoppingTime_eq δ m)

/-! ## 3. Measurability of the recommendation -/

/-- If the learner stops in round `n`, the firing condition holds in round `n`
(it holds at some `m ≤ n` by definition, and `n` is the least such `m`). -/
theorem chernoffStoppingTime_fires {δ : ℝ} {n : ℕ} {ω : ℕ → Fin k × ℝ}
    (hn : chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)) :
    ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω := by
  obtain ⟨m, hmn, hm⟩ := (chernoffStoppingTime_le_iff δ n ω).mp (le_of_eq hn)
  have hnm : ((n : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := hn ▸ sInf_le ⟨m, rfl, hm⟩
  have hnm' : n = m := le_antisymm (by exact_mod_cast hnm) hmn
  exact hnm' ▸ hm

/-- On the event that the learner stops in round `n`, the empirical maximiser is
unique, so the recommendation is the canonical maximiser. -/
theorem chernoffRecommendation_eq_argmax (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} {ω : ℕ → Fin k × ℝ} (hn : chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)) :
    chernoffRecommendation (k := k) δ ω = trajArgmax n ω := by
  have hfire : ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω :=
    chernoffStoppingTime_fires hn
  have hpos : trajGLR n ω ≠ 0 := by
    intro h0
    rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hfire
    exact absurd hfire (not_le.mpr (chernoffThreshold_pos hk hδ n))
  have hrec : chernoffRecommendation (k := k) δ ω = trajEmpiricalBestArm n ω := by
    rw [chernoffRecommendation, hn]
  rw [hrec, trajEmpiricalBestArm_eq_argmax_of_trajGLR_ne_zero n ω hpos]

omit [NeZero k] in
/-- `Exists.choose` depends only on the proposition, so a maximiser chosen from
equal data is the same arm. -/
theorem exists_max_image_choose_congr {f g : Fin k → ℝ} (h : f = g)
    (hf : ∃ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ x' ∈ (Finset.univ : Finset (Fin k)), f x' ≤ f x)
    (hg : ∃ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ x' ∈ (Finset.univ : Finset (Fin k)), g x' ≤ g x) :
    hf.choose = hg.choose := by
  subst h; rfl

/-- Two trajectories with the same empirical means at time `t` produce the same
(arbitrarily chosen) empirical best arm. -/
theorem trajEmpiricalBestArm_congr {t t' : ℕ} {ω ω' : ℕ → Fin k × ℝ}
    (h : (fun i : Fin k ↦ trajEmpiricalMean i t ω)
      = fun i : Fin k ↦ trajEmpiricalMean i t' ω') :
    trajEmpiricalBestArm t ω = trajEmpiricalBestArm t' ω' :=
  exists_max_image_choose_congr h _ _

/-- At time `0` all empirical means are the junk value `0`, so the fallback
recommendation is a constant. -/
theorem trajEmpiricalBestArm_zero_const (ω ω' : ℕ → Fin k × ℝ) :
    trajEmpiricalBestArm (k := k) 0 ω = trajEmpiricalBestArm (k := k) 0 ω' := by
  refine trajEmpiricalBestArm_congr ?_
  funext i
  simp [trajEmpiricalMean, trajPullCount]

/-- **The recommendation is `𝓕_τ`-measurable.** -/
theorem measurable_chernoffRecommendation (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    Measurable[(isBanditStoppingTime_chernoffStoppingTime (k := k) δ).measurableSpace]
      (chernoffRecommendation (k := k) δ) := by
  classical
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  have hτm := measurable_chernoffStoppingTime (k := k) δ
  -- ambient measurability
  have hamb : Measurable (chernoffRecommendation (k := k) δ) := by
    refine @measurable_to_countable' (Fin k) _ _ _ _ _ fun a ↦ ?_
    have hrw : (chernoffRecommendation (k := k) δ) ⁻¹' {a} =
        (⋃ n : ℕ, {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)} ∩
            {ω : ℕ → Fin k × ℝ | trajArgmax n ω = a}) ∪
          ({ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ⊤} ∩
            {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hω
        rcases eq_or_ne (chernoffStoppingTime (k := k) δ ω) ⊤ with htop | hne
        · refine Or.inr ⟨htop, ?_⟩
          rw [← hω, chernoffRecommendation, htop]
          rfl
        · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
          exact Or.inl ⟨n, hn.symm, by rw [← hω, chernoffRecommendation_eq_argmax hk hδ hn.symm]⟩
      · rintro (⟨n, hn, ha⟩ | ⟨hn, ha⟩)
        · rw [chernoffRecommendation_eq_argmax hk hδ hn, ha]
        · rw [chernoffRecommendation, hn]
          exact ha
    rw [hrw]
    refine MeasurableSet.union (MeasurableSet.iUnion fun n ↦ ?_) ?_
    · exact (hτm (measurableSet_singleton _)).inter
        ((banditFiltration k).le n _ ((measurable_trajArgmax n) (measurableSet_singleton a)))
    · rcases isEmpty_or_nonempty (ℕ → Fin k × ℝ) with _ | ⟨⟨ω₀⟩⟩
      · exact Subsingleton.measurableSet
      · by_cases hval : trajEmpiricalBestArm (k := k) 0 ω₀ = a
        · have h : {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a} = Set.univ := by
            ext ω; simp [trajEmpiricalBestArm_zero_const ω ω₀, hval]
          rw [h, Set.inter_univ]
          exact hτm (measurableSet_singleton _)
        · have h : {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a} = ∅ := by
            ext ω; simp [trajEmpiricalBestArm_zero_const ω ω₀, hval]
          rw [h, Set.inter_empty]
          exact MeasurableSet.empty
  refine @measurable_to_countable' (Fin k) _ _ _ hτ.measurableSpace _ fun i ↦ ?_
  refine ⟨hamb (measurableSet_singleton i), fun n ↦ ?_⟩
  show MeasurableSet[banditFiltration k n]
    ((chernoffRecommendation (k := k) δ) ⁻¹' {i} ∩
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)})
  have hrw : (chernoffRecommendation (k := k) δ) ⁻¹' {i} ∩
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)} =
      ⋃ m ∈ Finset.range (n + 1),
        ({ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} ∩
          {ω : ℕ → Fin k × ℝ | trajArgmax m ω = i}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Finset.mem_range, Nat.lt_succ_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hi, hle⟩
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m : ℕ) : ℕ∞) = chernoffStoppingTime (k := k) δ ω :=
        ENat.ne_top_iff_exists.mp fun htop ↦ by
          rw [htop] at hle; exact absurd hle (by simp)
      refine ⟨m, ?_, hm.symm, ?_⟩
      · rw [← hm] at hle; exact_mod_cast hle
      · rw [← hi, chernoffRecommendation_eq_argmax hk hδ hm.symm]
    · rintro ⟨m, hmn, hm, hi⟩
      refine ⟨by rw [chernoffRecommendation_eq_argmax hk hδ hm, hi], ?_⟩
      rw [hm]; exact_mod_cast hmn
  rw [hrw]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact ((banditFiltration k).mono hmn _ (measurableSet_chernoffStoppingTime_eq δ m)).inter
    ((banditFiltration k).mono hmn _ ((measurable_trajArgmax m) (measurableSet_singleton i)))

end Stop

end BanditAlgorithm

/-!
# The Chernoff inverse `f⁻¹(δ)`

`f(x) = e^{k−x}(x/k)^k` is continuous, equal to `1` at `x = k`, strictly
decreasing on `[k, ∞)`, and tends to `0`.  `chernoffInverse k δ` is defined as the
infimum of `{x ≥ k : f(x) ≤ δ}`, and this file proves the facts that make that
definition behave like an inverse:

* `chernoffF_chernoffInverse_le` — the infimum is attained, so `f(f⁻¹(δ)) ≤ δ`.
  This is what the soundness proof of L&S Lemma 33.7 actually consumes: the
  threshold really does deliver the promised confidence level.
* `chernoffInverse_le_of_le` — any admissible `x` bounds `f⁻¹(δ)` from above, so
  explicit thresholds can be plugged in.
* `chernoffInverse_antitone` — smaller confidence level, larger threshold.
* `chernoffF_antitoneOn` — `f` is decreasing on `[k, ∞)`, which is what makes
  `f⁻¹` an inverse rather than merely a lower bound.

Together with `chernoffThreshold_pos` these are all the properties of `β_t(δ)`
used anywhere in the Track-and-Stop analysis.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real Set

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Continuity and monotonicity of `f` -/

theorem continuous_chernoffF (k : ℕ) : Continuous (chernoffF k) := by
  unfold chernoffF
  fun_prop

/-- `f` is strictly decreasing on `[k, ∞)`: its logarithmic derivative is
`k/x − 1 < 0` there.  We prove the (equivalent, and sufficient) statement that
`f` is antitone on `[k, ∞)` directly from `log x ≤ x − 1`. -/
theorem chernoffF_le_chernoffF_of_le (hk : 0 < k) {x y : ℝ} (hx : (k : ℝ) ≤ x)
    (hxy : x ≤ y) : chernoffF k y ≤ chernoffF k x := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hkR hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
  -- compare logarithms
  have hlog : Real.log (chernoffF k y) ≤ Real.log (chernoffF k x) := by
    have hlx : Real.log (chernoffF k x)
        = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hx0.ne' hkR.ne']
    have hly : Real.log (chernoffF k y)
        = ((k : ℝ) - y) + k * (Real.log y - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hy0.ne' hkR.ne']
    rw [hlx, hly]
    -- `k (log y − log x) ≤ y − x` because `log(y/x) ≤ y/x − 1` and `x ≥ k`
    have hratio : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hy0.ne' hx0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hkx : (k : ℝ) * (y / x - 1) ≤ y - x := by
      have hyx : 0 ≤ y / x - 1 := by
        rw [sub_nonneg, le_div_iff₀ hx0]
        linarith
      calc (k : ℝ) * (y / x - 1) ≤ x * (y / x - 1) := by
            exact mul_le_mul_of_nonneg_right (le_trans hx (le_refl x)) hyx
        _ = y - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hratio (le_of_lt hkR)]
  have hposx : 0 < chernoffF k x := by
    rw [chernoffF]; positivity
  have hposy : 0 < chernoffF k y := by
    rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hposy hposx).mp hlog

/-! ## 2. The infimum is attained -/

theorem isClosed_chernoffInverse_set (k : ℕ) (δ : ℝ) :
    IsClosed {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} := by
  have h : {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}
      = Set.Ici (k : ℝ) ∩ chernoffF k ⁻¹' Set.Iic δ := by
    ext x; simp [and_comm]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Iic.preimage (continuous_chernoffF k))

/-- **The infimum defining `f⁻¹(δ)` is attained.** -/
theorem chernoffInverse_mem (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffInverse k δ ∈ {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  IsClosed.csInf_mem (isClosed_chernoffInverse_set k δ)
    (chernoffInverse_set_nonempty hk hδ) chernoffInverse_set_bddBelow

/-- **`f⁻¹(δ)` really is a threshold at confidence `δ`.** -/
theorem chernoffF_chernoffInverse_le (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffF k (chernoffInverse k δ) ≤ δ :=
  (chernoffInverse_mem hk hδ).2

/-- Above the threshold the Chernoff function stays below `δ`. -/
theorem chernoffF_le_of_chernoffInverse_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ)
    (hx : chernoffInverse k δ ≤ x) : chernoffF k x ≤ δ :=
  le_trans (chernoffF_le_chernoffF_of_le hk (chernoffInverse_mem hk hδ).1 hx)
    (chernoffF_chernoffInverse_le hk hδ)

/-! ## 3. Comparison -/

/-- Any admissible point bounds the threshold. -/
theorem chernoffInverse_le_of_le {δ x : ℝ} (hx : (k : ℝ) ≤ x) (hfx : chernoffF k x ≤ δ) :
    chernoffInverse k δ ≤ x :=
  csInf_le chernoffInverse_set_bddBelow ⟨hx, hfx⟩

/-- Smaller confidence level, larger threshold. -/
theorem chernoffInverse_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ') :
    chernoffInverse k δ' ≤ chernoffInverse k δ :=
  chernoffInverse_le_of_le (chernoffInverse_mem hk hδ).1
    (le_trans (chernoffF_chernoffInverse_le hk hδ) h)

/-- The threshold is `k` exactly at confidence level `1`, and at least `k`
always. -/
theorem chernoffInverse_one (hk : 0 < k) : chernoffInverse k 1 = (k : ℝ) :=
  le_antisymm (chernoffInverse_le_of_le le_rfl (le_of_eq (chernoffF_self hk)))
    (chernoffInverse_ge hk one_pos)

/-! ## 4. Monotonicity of the whole threshold -/

theorem chernoffThreshold_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ')
    (t : ℕ) : chernoffThreshold k δ' t ≤ chernoffThreshold k δ t := by
  unfold chernoffThreshold
  exact add_le_add_right (chernoffInverse_antitone hk hδ h) _

end BanditAlgorithm

/-!
# An explicit `O(log(1/δ))` bound on the Chernoff inverse

L&S use `f⁻¹(δ) = (1 + o(1)) log(1/δ)` to keep the leading constant of
Theorem 33.6 exact.  The `o(1)` is delicate, but the *order* is elementary and is
what every finiteness argument needs:

  `f⁻¹(δ) ≤ (k + log(1/δ)) / (1 − 1/e)`.

The proof is one application of `log y ≤ y/e` (itself `log(y/e) ≤ y/e − 1`):

  `log f(x) = (k − x) + k log(x/k) ≤ (k − x) + x/e = k − x(1 − 1/e)`,

so `f(x) ≤ δ` as soon as `x (1 − 1/e) ≥ k + log(1/δ)`; and any such `x` is
automatically `≥ k`, because `1 − 1/e < 1` and `log(1/δ) ≥ 0` for `δ ≤ 1`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `log y ≤ y / e`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := y / Real.exp 1)
    (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- The explicit form of `log f(x)` for `x > 0`. -/
theorem log_chernoffF (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    Real.log (chernoffF k x) = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_div hx.ne' hkR.ne']

/-- **The order bound.**  Every `x` with `x (1 − 1/e) ≥ k + log(1/δ)` is an
admissible threshold. -/
theorem chernoffF_le_of_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : (k : ℝ) + Real.log (1 / δ) ≤ x * (1 - (Real.exp 1)⁻¹)) :
    chernoffF k x ≤ δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  have hx0 : 0 < x := by
    by_contra hcon
    push_neg at hcon
    have : x * (1 - (Real.exp 1)⁻¹) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hfac.le
    linarith
  -- the key logarithmic estimate
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ := by
    rw [log_chernoffF hk hx0]
    have hbound : (k : ℝ) * (Real.log x - Real.log k) ≤ x * (Real.exp 1)⁻¹ := by
      have h := log_le_div_exp_one (y := x / (k : ℝ)) (by positivity)
      rw [Real.log_div hx0.ne' hkR.ne'] at h
      calc (k : ℝ) * (Real.log x - Real.log k) ≤ (k : ℝ) * (x / (k : ℝ) / Real.exp 1) :=
            mul_le_mul_of_nonneg_left h hkR.le
        _ = x * (Real.exp 1)⁻¹ := by field_simp
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    rw [hδlog] at hx
    nlinarith
  have hpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hpos hδ).mp hlog

/-- **`f⁻¹(δ) = O(k + log(1/δ))`.** -/
theorem chernoffInverse_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chernoffInverse k δ ≤ ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hfac1 : 1 - (Real.exp 1)⁻¹ ≤ 1 := by
    have : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set x : ℝ := ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) with hxdef
  have hxk : (k : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hfac]
    nlinarith
  refine chernoffInverse_le_of_le hxk (chernoffF_le_of_le hk hδ hδ1 ?_)
  rw [hxdef, div_mul_cancel₀ _ (ne_of_gt hfac)]

/-- Consequently the whole threshold is `O(k log(t²+t) + k + log(1/δ))`. -/
theorem chernoffThreshold_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    chernoffThreshold k δ t
      ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ))
        + ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  rw [chernoffThreshold]
  exact add_le_add_right (chernoffInverse_le_explicit hk hδ hδ1) _

end BanditAlgorithm

/-!
# The sharp lower bound on the threshold constant

`Solutions/ChernoffInverseBound.lean` bounds `f⁻¹(δ)` from *above* by
`(k + log(1/δ))/(1 − e⁻¹)`, which is what shows the sample complexity of
Chernoff's rule is `O(log(1/δ))`.  Turning the mixture martingale into the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7 needs
the opposite estimate, and needs it sharp.

Taking logarithms in `f(f⁻¹(δ)) ≤ δ` — that is, in
`e^{k−f⁻¹(δ)}(f⁻¹(δ)/k)^k ≤ δ` — gives directly

  `f⁻¹(δ) ≥ k + log(1/δ) + k·log(f⁻¹(δ)/k)`.

Dropping the last term (nonnegative, since `f⁻¹(δ) ≥ k`) recovers the crude
`f⁻¹(δ) ≥ k + log(1/δ)`, but the last term is exactly what one cannot afford to
drop: it grows like `k log log(1/δ)`, and that is the slack which pays for the
`½log(1 + cT)` prices of the mixture at prior variance `c ≈ log(1/δ)/k`.  Without
it the mixture argument fails for small `δ`, no matter how the variance is tuned.
-/

open Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `f⁻¹(δ) ≥ k`, restated. -/
theorem le_chernoffInverse (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ := (chernoffInverse_mem hk hδ).1

theorem chernoffInverse_pos' (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (le_chernoffInverse hk hδ)

/-- **The sharp lower bound on the threshold constant.**  Taking logarithms in
`f(f⁻¹(δ)) ≤ δ`. -/
theorem chernoffInverse_ge_sharp (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) + Real.log (1 / δ)
        + k * Real.log (chernoffInverse k δ / (k : ℝ))
      ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set β := chernoffInverse k δ with hβ
  have hβpos : 0 < β := chernoffInverse_pos' hk hδ
  have hf : chernoffF k β ≤ δ := chernoffF_chernoffInverse_le hk hδ
  have hfpos : 0 < chernoffF k β := by
    unfold chernoffF
    have : (0 : ℝ) < β / (k : ℝ) := by positivity
    positivity
  -- take logarithms
  have hlog : Real.log (chernoffF k β) ≤ Real.log δ := Real.log_le_log hfpos hf
  rw [log_chernoffF hk hβpos] at hlog
  have hdiv : Real.log (β / (k : ℝ)) = Real.log β - Real.log (k : ℝ) :=
    Real.log_div hβpos.ne' hkR.ne'
  have hinv : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  rw [hdiv, hinv]
  linarith

/-- The crude consequence: `f⁻¹(δ) ≥ k + log(1/δ)`. -/
theorem chernoffInverse_ge_add_log (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (k : ℝ) + Real.log (1 / δ) ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsharp := chernoffInverse_ge_sharp hk hδ
  have hge : (1 : ℝ) ≤ chernoffInverse k δ / (k : ℝ) :=
    (one_le_div hkR).mpr (le_chernoffInverse hk hδ)
  have hlog : 0 ≤ Real.log (chernoffInverse k δ / (k : ℝ)) := Real.log_nonneg hge
  nlinarith [mul_nonneg hkR.le hlog]

/-- The logarithmic slack, isolated: `f⁻¹(δ) − k − log(1/δ) ≥ k log(f⁻¹(δ)/k)`, and
`f⁻¹(δ)/k ≥ 1 + log(1/δ)/k`, so the slack is at least `k log(1 + log(1/δ)/k)`. -/
theorem chernoffInverse_slack (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (k : ℝ) + Real.log (1 / δ)
        + k * Real.log (1 + Real.log (1 / δ) / (k : ℝ))
      ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ1)
  have hsharp := chernoffInverse_ge_sharp hk hδ
  -- `f⁻¹(δ)/k ≥ 1 + log(1/δ)/k` from the crude bound
  have hcrude := chernoffInverse_ge_add_log hk hδ hδ1
  have hratio : 1 + Real.log (1 / δ) / (k : ℝ) ≤ chernoffInverse k δ / (k : ℝ) := by
    rw [le_div_iff₀ hkR, add_mul, one_mul, div_mul_cancel₀ _ hkR.ne']
    exact hcrude

  have hmono : Real.log (1 + Real.log (1 / δ) / (k : ℝ))
      ≤ Real.log (chernoffInverse k δ / (k : ℝ)) :=
    Real.log_le_log (by positivity) hratio
  nlinarith [mul_le_mul_of_nonneg_left hmono hkR.le]

end BanditAlgorithm

/-!
# When a linear statistic overtakes Chernoff's threshold

The sample-complexity half of Theorem 33.6 rests on a deterministic estimate.
Once the empirical allocation has settled, the generalised-likelihood-ratio
statistic grows linearly, `Z_t ≳ r·t` with `r ≈ c*(ν)⁻¹`, while the threshold
`β_t(δ) = k log(t²+t) + f⁻¹(δ)` grows only logarithmically in `t`.  So the two
must cross, and Chernoff's rule stops.  What the analysis needs is not just that
they cross but *where*: an explicit round, linear in `f⁻¹(δ)` and hence in
`log(1/δ)`, beyond which the linear statistic is ahead.

That is `linear_ge_threshold`: for

  `t ≥ max( (8K/r)², 2C/r )`,   `C ≥ K log 2 + β₀`,

one has `K log(t²+t) + β₀ ≤ r·t`.  The two conditions are the two ways the
threshold can be ahead — the logarithmic term (paid for by `t ≥ (8K/r)²`) and the
constant `β₀` (paid for by `t ≥ 2C/r`).  Since `β₀ = f⁻¹(δ)` enters only through
`C`, the crossing round is linear in `f⁻¹(δ)`, which is what makes
`E[τ_δ]/log(1/δ)` converge to `c*(ν)` and not to a larger constant.

The proof uses `log t ≤ 2√t`, which is `log √t ≤ √t − 1` — a cruder bound than
`log t ≤ t/e`, but the right one here, because the linear term must dominate a
*logarithm*, not a linear function.
-/

open Real

namespace BanditAlgorithm

/-! ## `log t ≤ 2√t` -/

theorem log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hsplit : Real.log t = 2 * Real.log (Real.sqrt t) := by
    conv_lhs => rw [← hsq]
    rw [Real.log_mul hs.ne' hs.ne']
    ring
  rw [hsplit]
  linarith

/-- `log(t² + t) ≤ log 2 + 2 log t` for `t ≥ 1`. -/
theorem log_sq_add_le {t : ℝ} (ht : 1 ≤ t) :
    Real.log (t ^ 2 + t) ≤ Real.log 2 + 2 * Real.log t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have hle : t ^ 2 + t ≤ 2 * t ^ 2 := by nlinarith
  calc Real.log (t ^ 2 + t) ≤ Real.log (2 * t ^ 2) :=
        Real.log_le_log (by positivity) hle
    _ = Real.log 2 + 2 * Real.log t := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring

/-! ## The crossing estimate -/

/-- **A linear statistic overtakes a logarithmic threshold, explicitly.**  For
`K ≥ 0`, `r > 0` and `C ≥ 0` with `K log 2 + β₀ ≤ C`, every `t ≥ 1` satisfying
`t ≥ (8K/r)²` and `t ≥ 2C/r` has `K log(t²+t) + β₀ ≤ r t`. -/
theorem linear_ge_threshold {K r C β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hC : 0 ≤ C)
    (hCge : K * Real.log 2 + β₀ ≤ C) {t : ℝ} (ht1 : 1 ≤ t)
    (ht2 : (8 * K / r) ^ 2 ≤ t) (ht3 : 2 * C / r ≤ t) :
    K * Real.log (t ^ 2 + t) + β₀ ≤ r * t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  -- the logarithmic part
  have hlog : K * Real.log (t ^ 2 + t) ≤ K * Real.log 2 + 4 * K * Real.sqrt t := by
    have h1 : Real.log (t ^ 2 + t) ≤ Real.log 2 + 2 * Real.log t := log_sq_add_le ht1
    have h2 : Real.log t ≤ 2 * Real.sqrt t := log_le_two_sqrt ht0
    nlinarith [mul_le_mul_of_nonneg_left h1 hK, mul_le_mul_of_nonneg_left h2 hK]
  -- the constant part is covered by `t ≥ 2C/r`
  have hconst : C ≤ r * t / 2 := by
    rw [div_le_iff₀ hr] at ht3
    linarith
  -- the square-root part is covered by `t ≥ (8K/r)²`
  have hroot : 4 * K * Real.sqrt t ≤ r * t / 2 := by
    have hKr : 8 * K / r ≤ Real.sqrt t := by
      have hnn : (0 : ℝ) ≤ 8 * K / r := by positivity
      have := Real.sqrt_le_sqrt ht2
      rwa [Real.sqrt_sq hnn] at this
    have h8 : 8 * K ≤ r * Real.sqrt t := by
      rw [div_le_iff₀ hr] at hKr
      linarith
    have : 8 * K * Real.sqrt t ≤ r * Real.sqrt t * Real.sqrt t :=
      mul_le_mul_of_nonneg_right h8 hs.le
    nlinarith [hsq]
  linarith

/-! ## The bound at the Chernoff threshold

Specialised to `K = k` and `β₀ = f⁻¹(δ)`, the crossing round is linear in
`f⁻¹(δ)`, hence — by `chernoffInverse_le_explicit` — in `log(1/δ)`. -/

theorem chernoffThreshold_le_linear {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {r : ℝ} (hr : 0 < r) {t : ℝ} (ht1 : 1 ≤ t)
    (ht2 : (8 * (k : ℝ) / r) ^ 2 ≤ t)
    (ht3 : 2 * ((k : ℝ) * Real.log 2 + chernoffInverse k δ) / r ≤ t) :
    (k : ℝ) * Real.log (t ^ 2 + t) + chernoffInverse k δ ≤ r * t := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hC : (0 : ℝ) ≤ (k : ℝ) * Real.log 2 + chernoffInverse k δ := by
    have h1 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : (0 : ℝ) < chernoffInverse k δ := chernoffInverse_pos' hk hδ
    positivity
  exact linear_ge_threshold hkR hr hC le_rfl ht1 ht2 ht3

/-- The crossing round in the form the sample-complexity argument uses: an
explicit `N` beyond which the linear statistic is ahead of the threshold at every
round. -/
theorem exists_crossing_round {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) {r : ℝ}
    (hr : 0 < r) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ t : ℝ, 1 ≤ t → N ≤ t →
      (k : ℝ) * Real.log (t ^ 2 + t) + chernoffInverse k δ ≤ r * t := by
  refine ⟨max ((8 * (k : ℝ) / r) ^ 2)
      (2 * ((k : ℝ) * Real.log 2 + chernoffInverse k δ) / r), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ (8 * (k : ℝ) / r) ^ 2 := sq_nonneg _
    exact le_trans h1 (le_max_left _ _)
  · intro t ht1 hN
    exact chernoffThreshold_le_linear hk hδ hr ht1
      (le_trans (le_max_left _ _) hN) (le_trans (le_max_right _ _) hN)

end BanditAlgorithm

/-!
# `f⁻¹(δ) ≤ (1 + ε) log(1/δ) + C(k, ε)`, uniformly in `δ`

`Solutions/ChernoffInverseBound.lean` proves the *order* bound
`f⁻¹(δ) ≤ (k + log(1/δ))/(1 − 1/e)`, whose multiplicative constant
`1/(1 − 1/e) ≈ 1.582` is fine for finiteness statements but destroys the leading
constant of Theorem 33.6.  `Solutions/ChernoffInverseAsymptotic.lean` proves
`f⁻¹(δ)/log(1/δ) → 1`, which has the right constant but only *eventually* in `δ`.

The sample-complexity argument needs both at once: a bound with multiplicative
constant `1 + ε` that holds for **every** `δ ∈ (0, 1]`, the excess being absorbed
into an additive constant depending on `k` and `ε` alone.  That is what this file
supplies:

  `f⁻¹(δ) ≤ (1 + ε) log(1/δ) + k + k(1 + ε) log((1 + ε)/ε)`.

Why one can do better than `1/(1 − 1/e)`: the order bound estimates `log y ≤ y/e`,
which is the *tangent* bound at `y = e` and so is only tight there.  Replacing it
by the tangent at an arbitrary point `c`,

  `log y ≤ y/c + log c − 1`,

makes the linear coefficient `1/c` as small as one likes, at the cost of the
additive `k log c`.  Taking `c = (1 + ε)/ε` makes the coefficient of `log(1/δ)`
come out to exactly `1 + ε`, and `k(1 + ε) log c` is then the price.  The price
blows up as `ε → 0`, which is the correct behaviour: `f⁻¹(δ) − log(1/δ) ∼
k log log(1/δ)` is genuinely unbounded, so no bound with `ε = 0` and a constant
can hold.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The shifted tangent bound on the logarithm -/

/-- `log y ≤ y/c + log c − 1` for all `y, c > 0`: the tangent to `log` at `y = c`.
Taking `c = e` recovers `log y ≤ y/e`. -/
theorem log_le_div_add_log_sub_one {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Real.log y ≤ y / c + Real.log c - 1 := by
  have h := Real.log_le_sub_one_of_pos (x := y / c) (div_pos hy hc)
  rw [Real.log_div hy.ne' hc.ne'] at h
  linarith

/-- The form in which the estimate is applied to `f`: `k log(x/k) ≤ x/c + k log c − k`. -/
theorem mul_log_div_le (hk : 0 < k) {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    (k : ℝ) * (Real.log x - Real.log k) ≤ x / c + (k : ℝ) * Real.log c - (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h := log_le_div_add_log_sub_one (y := x / (k : ℝ)) (by positivity) hc
  rw [Real.log_div hx.ne' hkR.ne'] at h
  have hmul : (k : ℝ) * (Real.log x - Real.log k)
      ≤ (k : ℝ) * (x / (k : ℝ) / c + Real.log c - 1) :=
    mul_le_mul_of_nonneg_left h hkR.le
  have hid : (k : ℝ) * (x / (k : ℝ) / c + Real.log c - 1)
      = x / c + (k : ℝ) * Real.log c - (k : ℝ) := by
    field_simp
  linarith [hid ▸ hmul]

/-! ## The additive constant -/

/-- `C(k, ε) = k + k(1 + ε) log((1 + ε)/ε)`, the additive price of forcing the
multiplicative constant down to `1 + ε`. -/
noncomputable def chernoffInverseConst (k : ℕ) (ε : ℝ) : ℝ :=
  (k : ℝ) + (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε)

theorem one_lt_tangentPoint {ε : ℝ} (hε : 0 < ε) : 1 < (1 + ε) / ε := by
  rw [lt_div_iff₀ hε]
  linarith

theorem log_tangentPoint_nonneg {ε : ℝ} (hε : 0 < ε) : 0 ≤ Real.log ((1 + ε) / ε) :=
  Real.log_nonneg (one_lt_tangentPoint hε).le

theorem chernoffInverseConst_ge (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    (k : ℝ) ≤ chernoffInverseConst k ε := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have h : 0 ≤ (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε) := by
    have := log_tangentPoint_nonneg hε
    positivity
  rw [chernoffInverseConst]
  linarith

theorem chernoffInverseConst_nonneg (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ chernoffInverseConst k ε :=
  le_trans (Nat.cast_nonneg k) (chernoffInverseConst_ge hk hε)

/-! ## The bound -/

/-- The admissibility criterion, in the sharpened form: any `x ≥ k` with
`x/(1 + ε) ≥ log(1/δ) + k log((1 + ε)/ε)` satisfies `f(x) ≤ δ`. -/
theorem chernoffF_le_of_sharp (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) {δ x : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : 0 < x)
    (hxb : Real.log (1 / δ) + (k : ℝ) * Real.log ((1 + ε) / ε) ≤ x / (1 + ε)) :
    chernoffF k x ≤ δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set c : ℝ := (1 + ε) / ε with hcdef
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  -- `1 - 1/c = 1/(1+ε)`
  have hinv : 1 - 1 / c = 1 / (1 + ε) := by
    rw [hcdef]
    field_simp
    ring
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ := by
    rw [log_chernoffF hk hx]
    have hb := mul_log_div_le hk hx hc0
    -- `log f(x) ≤ -x(1 - 1/c) + k log c`
    have hstep : ((k : ℝ) - x) + (k : ℝ) * (Real.log x - Real.log k)
        ≤ -(x * (1 - 1 / c)) + (k : ℝ) * Real.log c := by
      have hxc : x / c = x * (1 / c) := by ring
      nlinarith [hb, hxc]
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hkey : x * (1 - 1 / c) ≥ Real.log (1 / δ) + (k : ℝ) * Real.log c := by
      rw [hinv]
      have : x * (1 / (1 + ε)) = x / (1 + ε) := by ring
      rw [this]
      exact hxb
    linarith
  have hpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hpos hδ).mp hlog

/-- **`f⁻¹(δ) ≤ (1 + ε) log(1/δ) + C(k, ε)` for every `δ ∈ (0, 1]`.**  Unlike the
asymptotic version this holds at every confidence level, which is what the
sample-complexity bound needs: the additive constant is absorbed into the
`δ`-free random time, and the multiplicative `1 + ε` into the `ε`-slack of
Theorem 33.6. -/
theorem chernoffInverse_le_linear (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chernoffInverse k δ ≤ (1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set L : ℝ := Real.log (1 / δ) with hLdef
  set x : ℝ := (1 + ε) * L + chernoffInverseConst k ε with hxdef
  have hCk : (k : ℝ) ≤ chernoffInverseConst k ε := chernoffInverseConst_ge hk hε
  have hxk : (k : ℝ) ≤ x := by
    have : 0 ≤ (1 + ε) * L := by positivity
    rw [hxdef]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le hkR hxk
  refine chernoffInverse_le_of_le hxk (chernoffF_le_of_sharp hk hε hδ hδ1 hx0 ?_)
  -- `x/(1+ε) = L + (k + k(1+ε) log c)/(1+ε) ≥ L + k log c`
  have hlc : 0 ≤ Real.log ((1 + ε) / ε) := log_tangentPoint_nonneg hε
  rw [hxdef, chernoffInverseConst, le_div_iff₀ hε1]
  have hexpand : (Real.log (1 / δ) + (k : ℝ) * Real.log ((1 + ε) / ε)) * (1 + ε)
      = (1 + ε) * L + (k : ℝ) * (1 + ε) * Real.log ((1 + ε) / ε) := by
    rw [hLdef]; ring
  rw [hexpand]
  linarith

/-- The threshold in the same form: `β_n(δ) ≤ k log(n² + n) + (1 + ε) log(1/δ) + C(k, ε)`. -/
theorem chernoffThreshold_le_affine_log (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) :
    chernoffThreshold k δ n
      ≤ (k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ))
        + ((1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε) := by
  rw [chernoffThreshold]
  exact add_le_add_right (chernoffInverse_le_linear hk hε hδ hδ1) _

end BanditAlgorithm

/-!
# The crossing estimate with no loss in the constant

`Solutions/CrossingTime.lean` proves that a linear statistic overtakes the
logarithmic threshold at

  `t ≥ max( (8K/r)², 2(K log 2 + β₀)/r )`.

That is enough for *finiteness* of the stopping time, but the second condition
carries a factor `2` in front of `β₀`, and `β₀ = f⁻¹(δ)` is the term that grows
as `δ → 0`.  A factor `2` there is a factor `2` in the sample complexity, which
would turn Theorem 33.6's constant `c*(ν)` into `2 c*(ν)`.

The factor is an artefact of splitting `r t` into two equal halves, one for the
logarithm and one for the constant.  The logarithm needs only an *asymptotically
negligible* share, so the split can be made `(ε : 1)` instead of `(1 : 1)`:

  `r t = r' t + (r − r') t`,   `r' = εr/(1 + ε)`,   `r − r' = r/(1 + ε)`.

The first summand absorbs `K log(t² + t)` once `t` exceeds a threshold depending
on `K, r, ε` **but not on `β₀`**; the second absorbs `β₀` once
`t ≥ (1 + ε)β₀/r`.  The loss is now multiplicative-`(1 + ε)` on the `β₀` term and
purely additive elsewhere, which is exactly the shape Theorem 33.6 tolerates: the
`δ`-free part goes into the integrable random time `W`, and the `(1 + ε)` into
the `ε`-slack of the statement.
-/

open Real

namespace BanditAlgorithm

/-! ## The `δ`-free part of the crossing round -/

/-- `N(K, r, ε)`: the round beyond which the logarithmic term `K log(t² + t)` is
below the share `εr/(1 + ε)` of the linear statistic.  It does not involve the
threshold constant `β₀`, which is the whole point. -/
noncomputable def crossingConst (K r ε : ℝ) : ℝ :=
  max 1 (max ((8 * K * (1 + ε) / (ε * r)) ^ 2)
    (2 * K * Real.log 2 * (1 + ε) / (ε * r)))

theorem one_le_crossingConst (K r ε : ℝ) : 1 ≤ crossingConst K r ε :=
  le_max_left _ _

theorem crossingConst_nonneg (K r ε : ℝ) : 0 ≤ crossingConst K r ε :=
  le_trans zero_le_one (one_le_crossingConst K r ε)

/-! ## The sharp crossing lemma -/

/-- **A linear statistic overtakes a logarithmic threshold with no constant
loss.**  For `t ≥ N(K, r, ε)` and `t ≥ (1 + ε)β₀/r`,

  `K log(t² + t) + β₀ ≤ r t`.

The dependence on `β₀` is `(1 + ε)β₀/r`, not `2β₀/r`: the multiplicative loss can
be made arbitrarily small, at the cost of a larger `β₀`-free constant. -/
theorem linear_ge_threshold_sharp {K r ε β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) {t : ℝ}
    (hN : crossingConst K r ε ≤ t) (htβ : (1 + ε) * β₀ / r ≤ t) :
    K * Real.log (t ^ 2 + t) + β₀ ≤ r * t := by
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  set r' : ℝ := ε * r / (1 + ε) with hr'def
  have hr'0 : 0 < r' := by rw [hr'def]; positivity
  have ht1 : (1 : ℝ) ≤ t := le_trans (one_le_crossingConst K r ε) hN
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  -- the two conditions of the coarse estimate, at slope `r'`
  have hrw : 8 * K / r' = 8 * K * (1 + ε) / (ε * r) := by
    rw [hr'def]; field_simp
  have ht2 : (8 * K / r') ^ 2 ≤ t := by
    rw [hrw]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hrw2 : 2 * (K * Real.log 2) / r' = 2 * K * Real.log 2 * (1 + ε) / (ε * r) := by
    rw [hr'def]; field_simp
  have ht3 : 2 * (K * Real.log 2) / r' ≤ t := by
    rw [hrw2]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hClog : (0 : ℝ) ≤ K * Real.log 2 :=
    mul_nonneg hK (Real.log_nonneg (by norm_num))
  -- the logarithm is below the `ε`-share
  have hlog : K * Real.log (t ^ 2 + t) + 0 ≤ r' * t :=
    linear_ge_threshold hK hr'0 hClog (by linarith) ht1 ht2 ht3
  -- the constant is below the remaining share
  have hconst : β₀ ≤ r / (1 + ε) * t := by
    rw [div_le_iff₀ hr] at htβ
    rw [div_mul_eq_mul_div, le_div_iff₀ hε1]
    nlinarith
  have hsplit : r' * t + r / (1 + ε) * t = r * t := by
    rw [hr'def]
    field_simp
    ring
  linarith

/-! ## The estimate at integer rounds -/

/-- The integer form: `⌈N(K, r, ε)⌉ + ⌈(1 + ε)β₀/r⌉` rounds suffice, and the two
summands are respectively `β₀`-free and `δ`-free-of-everything-but-`β₀`. -/
theorem linear_ge_threshold_nat {K r ε β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) {n : ℕ}
    (hN : ⌈crossingConst K r ε⌉₊ ≤ n) (hnβ : ⌈(1 + ε) * β₀ / r⌉₊ ≤ n) :
    K * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + β₀ ≤ r * (n : ℝ) := by
  refine linear_ge_threshold_sharp hK hr hε hβ₀ ?_ ?_
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  · exact le_trans (Nat.le_ceil _) (by exact_mod_cast hnβ)

/-- Both conditions hold at the single round `⌈N⌉ + ⌈(1 + ε)β₀/r⌉`, and at every
later round. -/
theorem linear_ge_threshold_at_sum {K r ε β₀ : ℝ} (hK : 0 ≤ K) (hr : 0 < r)
    (hε : 0 < ε) (hβ₀ : 0 ≤ β₀) {n : ℕ}
    (hn : ⌈crossingConst K r ε⌉₊ + ⌈(1 + ε) * β₀ / r⌉₊ ≤ n) :
    K * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + β₀ ≤ r * (n : ℝ) :=
  linear_ge_threshold_nat hK hr hε hβ₀ (le_trans (Nat.le_add_right _ _) hn)
    (le_trans (Nat.le_add_left _ _) hn)

/-! ## Specialisation to Chernoff's threshold

`β_n(δ) = k log(n² + n) + f⁻¹(δ)`, and `f⁻¹(δ) ≤ (1 + ε) log(1/δ) + C(k, ε)` by
`chernoffInverse_le_linear`.  Both losses are `(1 + ε)`, so the crossing round is

  `⌈N(k, r, ε)⌉ + ⌈(1 + ε)((1 + ε) log(1/δ) + C(k, ε))/r⌉`,

whose `δ`-dependence is `(1 + ε)² log(1/δ)/r` — the constant `(1 + ε)²` tends to
`1`, which is what keeps Theorem 33.6 sharp. -/

variable {k : ℕ}

/-- The `δ`-dependent part of the crossing round: `(1 + ε)((1 + ε) log(1/δ) +
C(k, ε))/r`. -/
noncomputable def crossingBudget (k : ℕ) (r ε δ : ℝ) : ℝ :=
  (1 + ε) * ((1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε) / r

theorem crossingBudget_nonneg (hk : 0 < k) {r ε δ : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ crossingBudget k r ε δ := by
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  have hC : 0 ≤ chernoffInverseConst k ε := chernoffInverseConst_nonneg hk hε
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  rw [crossingBudget]
  positivity

/-- **Chernoff's threshold is below a linear statistic of slope `r` from round
`⌈N(k, r, ε)⌉ + ⌈budget⌉ on.** -/
theorem chernoffThreshold_le_of_crossing (hk : 0 < k) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {n : ℕ}
    (hn : ⌈crossingConst (k : ℝ) r ε⌉₊ + ⌈crossingBudget k r ε δ⌉₊ ≤ n) :
    chernoffThreshold k δ n ≤ r * (n : ℝ) := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hε1 : (0 : ℝ) < 1 + ε := by linarith
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set β₀ : ℝ := (1 + ε) * Real.log (1 / δ) + chernoffInverseConst k ε with hβdef
  have hβ0 : 0 ≤ β₀ := by
    have hC : 0 ≤ chernoffInverseConst k ε := chernoffInverseConst_nonneg hk hε
    rw [hβdef]; positivity
  have hbud : crossingBudget k r ε δ = (1 + ε) * β₀ / r := rfl
  have hmain : (k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + β₀ ≤ r * (n : ℝ) := by
    refine linear_ge_threshold_at_sum hkR hr hε hβ0 ?_
    rwa [hbud] at hn
  have hinv : chernoffInverse k δ ≤ β₀ := chernoffInverse_le_linear hk hε hδ hδ1
  rw [chernoffThreshold]
  linarith

end BanditAlgorithm

/-!
# The last round at which a sequence of events fails, and when it is integrable

Garivier & Kaufmann's Proposition 13 — the finiteness half of the sample
complexity of Track-and-Stop — is an instance of a single general fact, which
has nothing to do with bandits:

> Let `G 0, G 1, …` be events ("by round `m` the empirical quantities are already
> within `ξ` of their limits").  Let `T ω` be the first round from which *all*
> the `G m` hold.  Then
>
>   `∫⁻ T dμ ≤ ∑' m, (m + 1) · μ (G m)ᶜ`.

So `T` is integrable as soon as the failure probabilities `μ (G m)ᶜ` are summable
against `m` — for instance when they decay geometrically, which is what a
concentration inequality supplies.  This is the standard "`E[T] = ∑ P(T > n)`"
argument, and the bound above is what makes the `W` of
`chernoff_stopping_time_le_integrable_plus_linear` integrable.

The proof here deliberately avoids having to prove `T` measurable: the estimate
is established *pointwise*,

  `T ω ≤ ∑' m, (m + 1) · 1_{(G m)ᶜ}(ω)`,

and `lintegral_mono` needs no measurability of the smaller function.  The
pointwise bound is sharp in the only case that matters: if `ω` fails the events
exactly on a finite set with maximum `m₀`, then `T ω = m₀ + 1` and the `m₀`-th
summand alone is `m₀ + 1`.
-/

open MeasureTheory ENNReal NNReal

namespace BanditAlgorithm

variable {α : Type*} [MeasurableSpace α]

/-! ## The first round from which every event holds -/

/-- `T ω`, the first round from which `ω` belongs to every `G m`.  The junk value
`0` is returned when no such round exists; that case has measure zero in every
application, and the estimates below are stated so that it does no harm. -/
noncomputable def eventuallyIn (G : ℕ → Set α) (ω : α) : ℕ :=
  sInf {N : ℕ | ∀ n, N ≤ n → ω ∈ G n}

theorem eventuallyIn_le {G : ℕ → Set α} {ω : α} {N : ℕ}
    (h : ∀ n, N ≤ n → ω ∈ G n) : eventuallyIn G ω ≤ N :=
  Nat.sInf_le h

/-- Widening the events makes the settling time smaller — **provided the narrower
family does settle**.  The proviso is not decorative: `eventuallyIn` returns the
junk value `0` when its family never settles, so without it the inequality can
fail in the wrong direction on the non-settling set.  In the application that set
is null. -/
theorem eventuallyIn_mono {G G' : ℕ → Set α} {ω : α} (h : ∀ n, G n ⊆ G' n)
    (hne : ∃ N : ℕ, ∀ n, N ≤ n → ω ∈ G n) :
    eventuallyIn G' ω ≤ eventuallyIn G ω := by
  obtain ⟨N, hN⟩ := hne
  refine Nat.sInf_le fun n hn ↦ ?_
  exact h n (Nat.sInf_mem (⟨N, fun m hm ↦ hN m hm⟩ :
    {N : ℕ | ∀ n, N ≤ n → ω ∈ G n}.Nonempty) n hn)

theorem eventuallyIn_eq_zero {G : ℕ → Set α} {ω : α} (h : ∀ n, ω ∈ G n) :
    eventuallyIn G ω = 0 :=
  Nat.le_zero.mp (eventuallyIn_le fun n _ ↦ h n)

/-! ## The failure set -/

/-- The rounds at which `ω` fails the event. -/
def failureSet (G : ℕ → Set α) (ω : α) : Set ℕ := {m : ℕ | ω ∉ G m}

theorem eventuallyIn_le_of_bddAbove {G : ℕ → Set α} {ω : α}
    (hbdd : BddAbove (failureSet G ω)) (hne : (failureSet G ω).Nonempty) :
    eventuallyIn G ω ≤ sSup (failureSet G ω) + 1 := by
  refine eventuallyIn_le fun n hn ↦ ?_
  by_contra hcon
  have hmem : n ∈ failureSet G ω := hcon
  have : n ≤ sSup (failureSet G ω) := le_csSup hbdd hmem
  omega

/-! ## The pointwise estimate -/

/-- The weight `∑' m, (m + 1) · 1_{(G m)ᶜ}`, whose integral is
`∑' m, (m + 1) μ (G m)ᶜ`. -/
noncomputable def failureWeight (G : ℕ → Set α) (ω : α) : ℝ≥0∞ :=
  ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω

theorem le_failureWeight_of_mem {G : ℕ → Set α} {ω : α} {m : ℕ}
    (hm : ω ∉ G m) : ((m : ℝ≥0∞) + 1) ≤ failureWeight G ω := by
  have hterm : ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω
      = (m : ℝ≥0∞) + 1 := by
    rw [Set.indicator_of_mem (by exact hm), Pi.one_apply, mul_one]
  rw [← hterm]
  exact ENNReal.le_tsum m

/-- If infinitely many events fail, the weight is infinite. -/
theorem failureWeight_eq_top_of_infinite {G : ℕ → Set α} {ω : α}
    (h : (failureSet G ω).Infinite) : failureWeight G ω = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← ENNReal.iSup_natCast]
  refine iSup_le fun N ↦ ?_
  obtain ⟨F, hFsub, hFcard⟩ := h.exists_subset_card_eq N
  have hsum : ∑ m ∈ F, ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω
      ≤ failureWeight G ω := ENNReal.sum_le_tsum F
  refine le_trans ?_ hsum
  have hlb : ∀ m ∈ F,
      (1 : ℝ≥0∞) ≤ ((m : ℝ≥0∞) + 1) * (G m)ᶜ.indicator (1 : α → ℝ≥0∞) ω := by
    intro m hm
    have hmem : ω ∉ G m := hFsub hm
    rw [Set.indicator_of_mem (by exact hmem), Pi.one_apply, mul_one]
    exact le_add_self
  calc (N : ℝ≥0∞) = ∑ _m ∈ F, (1 : ℝ≥0∞) := by
        rw [Finset.sum_const, hFcard, nsmul_eq_mul, mul_one]
    _ ≤ _ := Finset.sum_le_sum hlb

/-- **The pointwise estimate.**  `T ω ≤ ∑' m, (m + 1) 1_{(G m)ᶜ}(ω)`. -/
theorem eventuallyIn_le_failureWeight (G : ℕ → Set α) (ω : α) :
    (eventuallyIn G ω : ℝ≥0∞) ≤ failureWeight G ω := by
  rcases (failureSet G ω).eq_empty_or_nonempty with hempty | hne
  · have hall : ∀ n, ω ∈ G n := by
      intro n
      by_contra hcon
      exact Set.eq_empty_iff_forall_notMem.mp hempty n hcon
    rw [eventuallyIn_eq_zero hall]
    simp
  · by_cases hbdd : BddAbove (failureSet G ω)
    · set m₀ : ℕ := sSup (failureSet G ω) with hm₀
      have hmem : m₀ ∈ failureSet G ω := Nat.sSup_mem hne hbdd
      have hT : eventuallyIn G ω ≤ m₀ + 1 := eventuallyIn_le_of_bddAbove hbdd hne
      calc (eventuallyIn G ω : ℝ≥0∞) ≤ ((m₀ + 1 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast Nat.cast_le.mpr hT
        _ = (m₀ : ℝ≥0∞) + 1 := by push_cast; ring
        _ ≤ failureWeight G ω := le_failureWeight_of_mem hmem
    · have hinf : (failureSet G ω).Infinite := fun hfin ↦ hbdd hfin.bddAbove
      rw [failureWeight_eq_top_of_infinite hinf]
      exact le_top

/-! ## The integral estimate -/

/-- The integral of the weight. -/
theorem lintegral_failureWeight (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : Measure α) :
    ∫⁻ ω, failureWeight G ω ∂μ = ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ := by
  simp only [failureWeight]
  rw [MeasureTheory.lintegral_tsum]
  · refine tsum_congr fun m ↦ ?_
    have hmeas : Measurable ((G m)ᶜ.indicator (1 : α → ℝ≥0∞)) :=
      measurable_const.indicator (hG m).compl
    rw [MeasureTheory.lintegral_const_mul _ hmeas]
    congr 1
    rw [MeasureTheory.lintegral_indicator_one (hG m).compl]
  · intro m
    exact ((measurable_const.indicator (hG m).compl).const_mul _).aemeasurable

/-- **The integral estimate.**  `∫ T ≤ ∑' m, (m + 1) μ (G m)ᶜ`, with no
measurability assumption on `T` itself. -/
theorem lintegral_eventuallyIn_le (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : Measure α) :
    ∫⁻ ω, (eventuallyIn G ω : ℝ≥0∞) ∂μ ≤ ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ := by
  rw [← lintegral_failureWeight G hG μ]
  exact lintegral_mono fun ω ↦ eventuallyIn_le_failureWeight G ω

/-- **Integrability criterion.**  `T` is integrable as soon as the failure
probabilities are summable against the round index. -/
theorem lintegral_eventuallyIn_ne_top (G : ℕ → Set α) (hG : ∀ m, MeasurableSet (G m))
    (μ : Measure α) (hsum : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ ≠ ⊤) :
    ∫⁻ ω, (eventuallyIn G ω : ℝ≥0∞) ∂μ ≠ ⊤ :=
  ne_top_of_le_ne_top hsum (lintegral_eventuallyIn_le G hG μ)

/-! ## A convenient sufficient condition: geometric decay

Concentration inequalities produce failure probabilities of the form
`C exp(-c m)`, or `C m^{-p}` with `p > 2`.  Both are summable against `m + 1`;
the first is packaged here because it is the shape the Chernoff analysis
produces. -/

/-- If `μ (G m)ᶜ ≤ C ρ^m` with `ρ < 1`, the failure weight is summable. -/
theorem tsum_lt_top_of_geometric {G : ℕ → Set α} {μ : Measure α} {C : ℝ≥0∞}
    (hC : C ≠ ⊤) {ρ : ℝ≥0} (hρ : ρ < 1)
    (hbd : ∀ m, μ (G m)ᶜ ≤ C * (ρ : ℝ≥0∞) ^ m) :
    ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ ≠ ⊤ := by
  have hmono : ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * μ (G m)ᶜ
      ≤ ∑' m : ℕ, ((m : ℝ≥0∞) + 1) * (C * (ρ : ℝ≥0∞) ^ m) :=
    ENNReal.tsum_le_tsum fun m ↦ mul_le_mul_left' (hbd m) _
  refine ne_top_of_le_ne_top ?_ hmono
  have hrw : ∀ m : ℕ, ((m : ℝ≥0∞) + 1) * (C * (ρ : ℝ≥0∞) ^ m)
      = C * (((m : ℝ≥0∞) + 1) * (ρ : ℝ≥0∞) ^ m) := by
    intro m; ring
  rw [tsum_congr hrw, ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top hC ?_
  -- `∑ (m+1) ρ^m` converges for `ρ < 1`; do the arithmetic in `ℝ≥0`
  set f : ℕ → ℝ≥0 := fun m ↦ ((m : ℝ≥0) + 1) * ρ ^ m with hfdef
  have hcoe : ∀ m : ℕ, ((f m : ℝ≥0) : ℝ≥0∞) = ((m : ℝ≥0∞) + 1) * (ρ : ℝ≥0∞) ^ m := by
    intro m
    rw [hfdef]
    push_cast
    ring
  have hreal : Summable fun m : ℕ ↦ ((f m : ℝ≥0) : ℝ) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (ρ : ℝ))
      (by rw [Real.norm_eq_abs, abs_of_nonneg ρ.coe_nonneg]; exact_mod_cast hρ)
    have hgeo : Summable fun m : ℕ ↦ (ρ : ℝ) ^ m :=
      summable_geometric_of_lt_one ρ.coe_nonneg (by exact_mod_cast hρ)
    refine (h.add hgeo).congr fun m ↦ ?_
    rw [hfdef]
    push_cast
    ring
  have hsummable : Summable f := by rw [← NNReal.summable_coe]; exact hreal
  have hne := (ENNReal.tsum_coe_ne_top_iff_summable (f := f)).mpr hsummable
  rwa [tsum_congr hcoe] at hne

end BanditAlgorithm

/-!
# From "the statistic is eventually linear" to a bound on Chernoff's stopping time

This is the deterministic skeleton of Garivier & Kaufmann's Theorem 14, and the
place where the three previous files meet.

Suppose that along a trajectory `ω` the generalised-likelihood-ratio statistic is
eventually above a line of slope `r`,

  `Z_n(ω) ≥ r n`  for all `n ≥ N(ω)`.                                   (∗)

Chernoff's rule stops as soon as `Z_n ≥ β_n(δ)`, and `Solutions/CrossingSharp.lean`
says that `β_n(δ) ≤ r n` from round `⌈N(k, r, ε)⌉ + ⌈budget(δ)⌉` on.  So the rule
has stopped by round

  `N(ω) + ⌈N(k, r, ε)⌉ + ⌈budget(δ)⌉`,

the first two summands being free of `δ` and the third free of `ω`.  That is
exactly the shape `τ_δ ≤ W + (linear in log(1/δ))` demanded by
`chernoff_stopping_time_le_integrable_plus_linear`: `W` is the `δ`-free part.

The random part `N(ω)` is `eventuallyIn` of the events `{Z_n ≥ r n}`, so
`Solutions/HittingTime.lean` bounds its integral by `∑ (n+1) P(Z_n < r n)`, and
`W` is integrable as soon as those probabilities are summable against `n`.  The
concentration estimate that supplies the summability is the one genuinely
probabilistic input still missing; everything else in the chain is here.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## The event that the statistic is above the line -/

/-- `{ω | Z_n(ω) ≥ r n}`: the statistic is above the line of slope `r` at round `n`. -/
def glrLinearEvent (r : ℝ) (n : ℕ) : Set (ℕ → Fin k × ℝ) :=
  {ω | ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω}

/-- The `δ`-free part of the crossing round: the first round from which the
statistic stays above the line, plus the `β₀`-free constant of the crossing
estimate. -/
noncomputable def crossWitness (k : ℕ) [NeZero k] (r ε : ℝ) (ω : ℕ → Fin k × ℝ) : ℕ :=
  eventuallyIn (glrLinearEvent (k := k) r) ω + ⌈crossingConst (k : ℝ) r ε⌉₊

theorem le_crossWitness (r ε : ℝ) (ω : ℕ → Fin k × ℝ) :
    ⌈crossingConst (k : ℝ) r ε⌉₊ ≤ crossWitness k r ε ω :=
  Nat.le_add_left _ _

/-- On a trajectory along which the statistic is eventually above the line, it is
above the line at every round past `eventuallyIn`. -/
theorem mem_glrLinearEvent_of_le {r : ℝ} {ω : ℕ → Fin k × ℝ}
    (hω : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω)
    {n : ℕ} (hn : eventuallyIn (glrLinearEvent (k := k) r) ω ≤ n) :
    ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω := by
  obtain ⟨N, hN⟩ := hω
  have hnonempty : {N : ℕ | ∀ n, N ≤ n → ω ∈ glrLinearEvent (k := k) r n}.Nonempty :=
    ⟨N, fun n hn ↦ hN n hn⟩
  have hmem := Nat.sInf_mem hnonempty
  exact hmem n hn

/-! ## The bound on the stopping time -/

/-- **Chernoff's rule stops by round `W(ω) + ⌈budget(δ)⌉`.**  The first summand
does not depend on `δ`, the second does not depend on `ω`. -/
theorem chernoffStoppingTime_le_crossWitness_add (hk : 0 < k) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ω : ℕ → Fin k × ℝ}
    (hω : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω) :
    chernoffStoppingTime (k := k) δ ω
      ≤ ((crossWitness k r ε ω + ⌈crossingBudget k r ε δ⌉₊ : ℕ) : ℕ∞) := by
  set n : ℕ := crossWitness k r ε ω + ⌈crossingBudget k r ε δ⌉₊ with hndef
  refine (chernoffStoppingTime_le_iff δ n ω).mpr ⟨n, le_rfl, ?_⟩
  -- the threshold is below the line at round `n`
  have hcross : chernoffThreshold k δ n ≤ r * (n : ℝ) := by
    refine chernoffThreshold_le_of_crossing hk hr hε hδ hδ1 ?_
    rw [hndef, crossWitness]
    omega
  -- and the line is below the statistic at round `n`
  have hline : ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω := by
    refine mem_glrLinearEvent_of_le hω ?_
    rw [hndef, crossWitness]
    omega
  exact le_trans (ENNReal.ofReal_le_ofReal hcross) hline

/-! ## Integrability of the `δ`-free part -/

/-- The integral of `W` splits into the integral of the hitting time and a
constant. -/
theorem lintegral_crossWitness_le {r ε : ℝ} (μ : Measure (ℕ → Fin k × ℝ))
    [IsProbabilityMeasure μ] :
    ∫⁻ ω, (crossWitness k r ε ω : ℝ≥0∞) ∂μ
      ≤ (∫⁻ ω, (eventuallyIn (glrLinearEvent (k := k) r) ω : ℝ≥0∞) ∂μ)
        + (⌈crossingConst (k : ℝ) r ε⌉₊ : ℝ≥0∞) := by
  have hpt : ∀ ω, (crossWitness k r ε ω : ℝ≥0∞)
      = (eventuallyIn (glrLinearEvent (k := k) r) ω : ℝ≥0∞)
        + (⌈crossingConst (k : ℝ) r ε⌉₊ : ℝ≥0∞) := by
    intro ω
    rw [crossWitness]
    push_cast
    ring
  calc ∫⁻ ω, (crossWitness k r ε ω : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ((eventuallyIn (glrLinearEvent (k := k) r) ω : ℝ≥0∞)
          + (⌈crossingConst (k : ℝ) r ε⌉₊ : ℝ≥0∞)) ∂μ := by
        exact lintegral_congr hpt
    _ ≤ (∫⁻ ω, (eventuallyIn (glrLinearEvent (k := k) r) ω : ℝ≥0∞) ∂μ)
          + (⌈crossingConst (k : ℝ) r ε⌉₊ : ℝ≥0∞) := by
        rw [MeasureTheory.lintegral_add_right _ measurable_const,
          MeasureTheory.lintegral_const, measure_univ, mul_one]

/-- **`W` is integrable as soon as the failure probabilities are summable.**  This
is the finiteness half of Garivier & Kaufmann's Proposition 13, reduced to a
statement about `P(Z_n < r n)` alone. -/
theorem lintegral_crossWitness_ne_top {r ε : ℝ} (μ : Measure (ℕ → Fin k × ℝ))
    [IsProbabilityMeasure μ]
    (hmeas : ∀ n, MeasurableSet (glrLinearEvent (k := k) r n))
    (hsum : ∑' n : ℕ, ((n : ℝ≥0∞) + 1) * μ (glrLinearEvent (k := k) r n)ᶜ ≠ ⊤) :
    ∫⁻ ω, (crossWitness k r ε ω : ℝ≥0∞) ∂μ ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_crossWitness_le μ)
  refine ENNReal.add_ne_top.mpr ⟨?_, ENNReal.natCast_ne_top _⟩
  exact lintegral_eventuallyIn_ne_top _ hmeas μ hsum

/-! ## The `δ`-dependence, in the form Theorem 33.6 wants

`budget(δ) = (1 + ε)((1 + ε) log(1/δ) + C(k, ε))/r`.  Writing `1/r = (1 + ε₁)c*`
this is `(1 + ε)²(1 + ε₁) c* log(1/δ) + (1 + ε)C(k, ε)/r`: a multiple of
`log(1/δ)` whose constant tends to `c*` as `ε, ε₁ → 0`, plus a `δ`-free constant
that joins `W`. -/

theorem crossingBudget_eq (k : ℕ) (r ε δ : ℝ) :
    crossingBudget k r ε δ
      = (1 + ε) * (1 + ε) / r * Real.log (1 / δ)
        + (1 + ε) * chernoffInverseConst k ε / r := by
  rw [crossingBudget]
  ring

/-- The ceiling splits: `⌈budget⌉ ≤ ⌈A log(1/δ)⌉ + ⌈B⌉`, with `B` free of `δ`. -/
theorem ceil_crossingBudget_le (hk : 0 < k) {r ε δ : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ⌈crossingBudget k r ε δ⌉₊
      ≤ ⌈(1 + ε) * (1 + ε) / r * Real.log (1 / δ)⌉₊
        + ⌈(1 + ε) * chernoffInverseConst k ε / r⌉₊ := by
  rw [crossingBudget_eq]
  exact Nat.ceil_add_le _ _

end BanditAlgorithm

/-!
# The settling time of the empirical quantities

Garivier & Kaufmann's Proposition 13 is a statement about one random time:

  `T_ξ = inf { T : for all t ≥ T, |w_i(t) − α_i| ≤ ξ and |μ̂_i(t) − μ_i| ≤ ξ }`,

the round from which the empirical allocation and the empirical means have
settled to within `ξ` of their limits.  Proposition 13 says `E[T_ξ] < ∞` for the
D-Tracking sampling rule.  Everything downstream — Theorem 14, and with it the
expected sample complexity of Track-and-Stop — uses only that one fact about the
sampling rule.

This file names `T_ξ` (`settlingTime`) and records the one implication that makes
it the right object: the settling event is contained in the event that the GLR
statistic is above a line, so `T_ξ` dominates the crossing time of
`Solutions/StoppingBridge.lean`, and `E[T_ξ] < ∞` gives the integrable `W`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Topology

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## The settling event and the settling time -/

/-- `{ω | round n ≥ 1 and both the allocation and the means are within `ξ`}`. -/
def settlingEvent (α μvec : Fin k → ℝ) (ξ : ℝ) (n : ℕ) : Set (ℕ → Fin k × ℝ) :=
  {ω | 0 < n ∧ (∀ i, |trajAllocation i n ω - α i| ≤ ξ) ∧
    (∀ i, |trajEmpiricalMean i n ω - μvec i| ≤ ξ)}

/-- `T_ξ`, the first round from which the empirical quantities stay within `ξ`. -/
noncomputable def settlingTime (α μvec : Fin k → ℝ) (ξ : ℝ)
    (ω : ℕ → Fin k × ℝ) : ℕ :=
  eventuallyIn (settlingEvent α μvec ξ) ω

/-! ## Settling implies the statistic is above the line -/

/-- If the window `ξ` was chosen so that the perturbed pair rates all exceed `r`,
then settling at round `n` puts the statistic above the line of slope `r`. -/
theorem settlingEvent_subset_glrLinearEvent {μvec α : Fin k → ℝ} {istar : Fin k}
    {ξ r : ℝ} (hξ : 0 < ξ) (hξα : ∀ i, ξ < α i)
    (hξgap : ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j)
    (hξrate : ∀ j, j ≠ istar → r ≤ pairRateLower α μvec ξ istar j) (n : ℕ) :
    settlingEvent α μvec ξ n ⊆ glrLinearEvent (k := k) r n := by
  rintro ω ⟨hn, hw, hm⟩
  have h := trajGLR_ge_of_close hn hξ.le hw hm hξα hξgap hξrate
  show ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω
  rwa [mul_comm (r : ℝ) ((n : ℕ) : ℝ)]

/-- Hence the crossing time is dominated by the settling time. -/
theorem eventuallyIn_glrLinearEvent_le_settlingTime {μvec α : Fin k → ℝ}
    {istar : Fin k} {ξ r : ℝ} (hξ : 0 < ξ) (hξα : ∀ i, ξ < α i)
    (hξgap : ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j)
    (hξrate : ∀ j, j ≠ istar → r ≤ pairRateLower α μvec ξ istar j)
    {ω : ℕ → Fin k × ℝ}
    (hω : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ω ∈ settlingEvent α μvec ξ n) :
    eventuallyIn (glrLinearEvent (k := k) r) ω ≤ settlingTime α μvec ξ ω :=
  eventuallyIn_mono (settlingEvent_subset_glrLinearEvent hξ hξα hξgap hξrate) hω

/-- And the crossing time is integrable whenever the settling time is. -/
theorem lintegral_eventuallyIn_glrLinearEvent_ne_top {μvec α : Fin k → ℝ}
    {istar : Fin k} {ξ r : ℝ} (hξ : 0 < ξ) (hξα : ∀ i, ξ < α i)
    (hξgap : ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j)
    (hξrate : ∀ j, j ≠ istar → r ≤ pairRateLower α μvec ξ istar j)
    (P : Measure (ℕ → Fin k × ℝ))
    (hae : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ω ∈ settlingEvent α μvec ξ n)
    (hT : ∫⁻ ω, (settlingTime α μvec ξ ω : ℝ≥0∞) ∂P ≠ ⊤) :
    ∫⁻ ω, (eventuallyIn (glrLinearEvent (k := k) r) ω : ℝ≥0∞) ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top hT (lintegral_mono_ae ?_)
  filter_upwards [hae] with ω hω
  exact_mod_cast Nat.cast_le.mpr
    (eventuallyIn_glrLinearEvent_le_settlingTime hξ hξα hξgap hξrate hω)

/-- Along a trajectory that eventually settles, the statistic is eventually above
the line — the hypothesis of `chernoffStoppingTime_le_crossWitness_add`. -/
theorem exists_eventually_of_settles {μvec α : Fin k → ℝ} {istar : Fin k}
    {ξ r : ℝ} (hξ : 0 < ξ) (hξα : ∀ i, ξ < α i)
    (hξgap : ∀ j, j ≠ istar → 2 * ξ < μvec istar - μvec j)
    (hξrate : ∀ j, j ≠ istar → r ≤ pairRateLower α μvec ξ istar j)
    {ω : ℕ → Fin k × ℝ}
    (hω : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ω ∈ settlingEvent α μvec ξ n) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω := by
  obtain ⟨N, hN⟩ := hω
  exact ⟨N, fun n hn ↦ settlingEvent_subset_glrLinearEvent hξ hξα hξgap hξrate n (hN n hn)⟩

/-! ## Settling is what the tracking hypothesis provides, qualitatively

Convergence of the empirical quantities is exactly "for every `ξ > 0` the
settling event eventually holds"; the extra content of Proposition 13 is that the
settling time is *integrable*, not merely finite. -/

theorem exists_settles_of_tendsto {μvec α : Fin k → ℝ} {ξ : ℝ} (hξ : 0 < ξ)
    {ω : ℕ → Fin k × ℝ}
    (hwlim : ∀ i, Tendsto (fun t : ℕ ↦ trajAllocation i t ω) atTop (𝓝 (α i)))
    (hmlim : ∀ i, Tendsto (fun t : ℕ ↦ trajEmpiricalMean i t ω) atTop (𝓝 (μvec i))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ω ∈ settlingEvent α μvec ξ n := by
  classical
  have hw : ∀ᶠ t : ℕ in atTop, ∀ i, |trajAllocation i t ω - α i| ≤ ξ := by
    rw [Filter.eventually_all]
    intro i
    have := (Metric.tendsto_nhds.mp (hwlim i)) ξ hξ
    exact this.mono fun t ht ↦ le_of_lt (by rwa [Real.dist_eq] at ht)
  have hm : ∀ᶠ t : ℕ in atTop, ∀ i, |trajEmpiricalMean i t ω - μvec i| ≤ ξ := by
    rw [Filter.eventually_all]
    intro i
    have := (Metric.tendsto_nhds.mp (hmlim i)) ξ hξ
    exact this.mono fun t ht ↦ le_of_lt (by rwa [Real.dist_eq] at ht)
  obtain ⟨N, hN⟩ := ((hw.and hm).and (eventually_gt_atTop 0)).exists_forall_of_atTop
  refine ⟨N, fun n hn ↦ ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hN n hn
  exact ⟨h3, h1, h2⟩

end BanditAlgorithm

/-!
# The characteristic time of a Gaussian bandit is finite, with an explicit bound

Plugging the *uniform* allocation into the closed form of
`gaussian_bai_characteristic_time_formula` gives

  `c*(ν)⁻¹ ≥ min_{j ≠ i*} Δ_j² / (4k)`,   i.e.   `c*(ν) ≤ 4k / Δ_min²`.

Finiteness is not a technicality: L&S Theorem 33.6 and its lower half both speak
of `c*(ν).toReal`, and `ℝ≥0∞`-to-`ℝ` coercion silently sends `∞` to `0`, so
without `c*(ν) ≠ ∞` the statement of the theorem would be about the wrong
quantity.  The bound `4k/Δ_min²` is the familiar "the harder the gaps, the longer
it takes" scaling, and matches the `H₂`-style complexities of the fixed-budget
chapters.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The uniform allocation. -/
noncomputable def uniformAllocation (k : ℕ) : Fin k → ℝ≥0 := fun _ ↦ (k : ℝ≥0)⁻¹

theorem uniformAllocation_pos (hk : 0 < k) (i : Fin k) : 0 < uniformAllocation k i := by
  have : (0 : ℝ≥0) < (k : ℝ≥0) := by exact_mod_cast hk
  simpa [uniformAllocation] using this

theorem sum_uniformAllocation (hk : 0 < k) : ∑ i, uniformAllocation k i = 1 := by
  have hkne : (k : ℝ≥0) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hk.ne'
  simp only [uniformAllocation, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ hkne

/-- The pair cost of the uniform allocation. -/
theorem pairCost_uniformAllocation (hk : 0 < k) (μvec : Fin k → ℝ) (istar j : Fin k) :
    pairCost (uniformAllocation k) μvec istar j
      = (μvec istar - μvec j) ^ 2 / (4 * (k : ℝ)) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  unfold pairCost uniformAllocation
  have hcast : (((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = ((k : ℝ))⁻¹ := by
    simp
  rw [hcast]
  field_simp
  ring

/-- **The characteristic time is finite.**  Any positive lower bound on the gaps
gives an explicit bound on `c*(ν)`. -/
theorem baiComplexity_le_of_gap_le [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {Δ : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j) :
    baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k)))
      ≤ ENNReal.ofReal (4 * (k : ℝ) / Δ ^ 2) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- the uniform allocation already achieves `Δ²/(4k)`
  have hval : ENNReal.ofReal (Δ ^ 2 / (4 * (k : ℝ)))
      ≤ ⨅ j ∈ {j : Fin k | j ≠ istar},
          ENNReal.ofReal (pairCost (uniformAllocation k) μvec istar j) := by
    refine le_iInf₂ fun j hj ↦ ?_
    rw [pairCost_uniformAllocation hk]
    refine ENNReal.ofReal_le_ofReal ?_
    have hgj : Δ ≤ μvec istar - μvec j := hgap j hj
    have : Δ ^ 2 ≤ (μvec istar - μvec j) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_right this (by positivity) |>.trans_eq rfl
  have hformula := inner_gaussian_eq hstar (uniformAllocation_pos hk)
  have hle : ENNReal.ofReal (Δ ^ 2 / (4 * (k : ℝ)))
      ≤ ⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i) := by
    refine le_trans (le_trans hval (le_of_eq hformula.symm)) ?_
    exact le_iSup₂ (f := fun α (_ : α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1}) ↦
      ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
        ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i))
      (uniformAllocation k) (sum_uniformAllocation hk)
  rw [baiComplexity]
  refine le_trans (ENNReal.inv_le_inv.mpr hle) (le_of_eq ?_)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Finiteness of the characteristic time.** -/
theorem baiComplexity_ne_top [NeZero k] {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) :
    baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) ≠ ⊤ := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  by_cases hk1 : ∀ j : Fin k, j = istar
  · -- a single arm: the alternative set is empty, so the infimum is `∞` and `c* = 0`
    have hempty : baiAlternatives (Set.range (gaussianBandit (k := k)))
        (gaussianBandit μvec) = ∅ := by
      ext ν'
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro hν'
      obtain ⟨b, rfl⟩ : ∃ b : Fin k → ℝ, gaussianBandit b = ν' := hν'.1
      obtain ⟨j, hj⟩ := (mem_baiAlternatives_iff_of_unique hstar b).mp hν'
      rw [hk1 j] at hj
      exact absurd hj (lt_irrefl _)
    have : baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) = 0 := by
      rw [baiComplexity]
      have htop : (⨆ α ∈ {α : Fin k → ℝ≥0 | ∑ i, α i = 1},
          ⨅ ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit μvec),
            ∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit μvec).P i) (ν'.P i)) = ⊤ := by
        refine le_antisymm le_top ?_
        refine le_iSup₂_of_le (uniformAllocation k) (sum_uniformAllocation hk) ?_
        rw [hempty]
        simp
      rw [htop, ENNReal.inv_top]
    rw [this]
    exact ENNReal.zero_ne_top
  · -- at least two arms: use the explicit bound with the smallest gap
    push_neg at hk1
    obtain ⟨j₀, hj₀⟩ := hk1
    set S : Finset (Fin k) := Finset.univ.filter (fun j ↦ j ≠ istar) with hS
    have hSne : S.Nonempty := ⟨j₀, by simp [hS, hj₀]⟩
    set Δ : ℝ := S.inf' hSne (fun j ↦ μvec istar - μvec j) with hΔdef
    have hΔ : 0 < Δ := by
      rw [hΔdef, Finset.lt_inf'_iff]
      intro j hj
      have : j ≠ istar := by simpa [hS] using hj
      linarith [hstar j this]
    have hgap : ∀ j, j ≠ istar → Δ ≤ μvec istar - μvec j := by
      intro j hj
      exact Finset.inf'_le _ (by simp [hS, hj])
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (baiComplexity_le_of_gap_le hstar hΔ hgap)

end BanditAlgorithm

/-!
# The optimal allocation realises the slope `1/c*(ν)`

`IsOptimalAllocation ν 𝓔 α` says that the inner infimum of L&S Eq. (33.4)
evaluated at `α` equals `c*(ν)⁻¹`.  For a Gaussian bandit with a unique best arm
that inner infimum has the closed form `min_{j ≠ i*} pairCost(α, μ)`
(`inner_gaussian_eq`), so

  `min_{j ≠ i*} pairCost(α, μ) = c*(ν)⁻¹`,

and in particular every individual pair cost is at least `c*(ν)⁻¹`.  That is the
number the crossing argument needs: by `Solutions/GLRRate.lean` the GLR statistic
under `α` is eventually above `t · min_j pairCost = t/c*(ν)`, so Chernoff's rule
stops at a round proportional to `c*(ν) log(1/δ)` — the constant of Theorem 33.6.

This file does the `ℝ≥0∞`-to-`ℝ` bookkeeping: that `c*(ν)` is finite and nonzero,
and that the real number `(c*(ν).toReal)⁻¹` is a lower bound for every pair cost.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## The infimum is attained and finite -/

/-- Under an optimal allocation with positive weights the inner infimum equals the
minimum of the pair costs. -/
theorem iInf_pairCost_eq_inv_complexity {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i)
    (hopt : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α) :
    (⨅ j ∈ {j : Fin k | j ≠ istar}, ENNReal.ofReal (pairCost α μvec istar j))
      = (baiComplexity (gaussianBandit μvec)
          (Set.range (gaussianBandit (k := k))))⁻¹ := by
  rw [← inner_gaussian_eq hstar hα]
  exact hopt.2

/-- Every pair cost dominates `c*(ν)⁻¹`. -/
theorem inv_complexity_le_ofReal_pairCost {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i)
    (hopt : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α)
    {j : Fin k} (hj : j ≠ istar) :
    (baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))))⁻¹
      ≤ ENNReal.ofReal (pairCost α μvec istar j) := by
  rw [← iInf_pairCost_eq_inv_complexity hstar hα hopt]
  exact iInf₂_le (f := fun j (_ : j ∈ {j : Fin k | j ≠ istar}) ↦
    ENNReal.ofReal (pairCost α μvec istar j)) j hj

/-- With at least two arms the characteristic time is strictly positive: some
competing arm exists, and its pair cost is finite. -/
theorem baiComplexity_pos {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i)
    (hopt : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α)
    {j : Fin k} (hj : j ≠ istar) :
    0 < baiComplexity (gaussianBandit μvec) (Set.range (gaussianBandit (k := k))) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hle := inv_complexity_le_ofReal_pairCost hstar hα hopt hj
  rw [hzero, ENNReal.inv_zero] at hle
  exact absurd (le_antisymm le_top hle) (ENNReal.ofReal_ne_top)

/-! ## The real slope -/

/-- `c*(ν)` as a real number. -/
noncomputable def baiComplexityReal (ν : StochasticBandit k)
    (𝓔 : Set (StochasticBandit k)) : ℝ :=
  (baiComplexity ν 𝓔).toReal

/-- **The slope realised by an optimal allocation.**  `1/c*(ν) ≤ pairCost(α, μ)`
for every competing arm. -/
theorem inv_baiComplexityReal_le_pairCost {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i)
    (hopt : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α)
    {j : Fin k} (hj : j ≠ istar) :
    (baiComplexityReal (gaussianBandit μvec)
        (Set.range (gaussianBandit (k := k))))⁻¹ ≤ pairCost α μvec istar j := by
  have hne : baiComplexity (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) ≠ ⊤ := baiComplexity_ne_top hstar
  have hpos := baiComplexity_pos hstar hα hopt hj
  have hle := inv_complexity_le_ofReal_pairCost hstar hα hopt hj
  have hcost : 0 ≤ pairCost α μvec istar j := pairCost_nonneg istar j
  set c : ℝ≥0∞ := baiComplexity (gaussianBandit μvec)
    (Set.range (gaussianBandit (k := k))) with hc
  have htoReal : (baiComplexityReal (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))))⁻¹ = (c⁻¹).toReal := by
    rw [baiComplexityReal, ← hc, ENNReal.toReal_inv]
  rw [htoReal]
  calc (c⁻¹).toReal ≤ (ENNReal.ofReal (pairCost α μvec istar j)).toReal := by
        refine ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = pairCost α μvec istar j := ENNReal.toReal_ofReal hcost

theorem baiComplexityReal_pos {μvec : Fin k → ℝ} {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar) {α : Fin k → ℝ≥0}
    (hα : ∀ i, 0 < α i)
    (hopt : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α)
    {j : Fin k} (hj : j ≠ istar) :
    0 < baiComplexityReal (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) := by
  have hne : baiComplexity (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) ≠ ⊤ := baiComplexity_ne_top hstar
  have hpos := baiComplexity_pos hstar hα hopt hj
  rw [baiComplexityReal]
  exact ENNReal.toReal_pos hpos.ne' hne

end BanditAlgorithm

/-!
# Theorem 14: the stopping time is a `δ`-free integrable time plus `c*(ν) log(1/δ)`

This assembles the whole deterministic chain.  Given

* an optimal allocation `α` with strictly positive weights,
* the settling time `T_ξ` of `Solutions/SettlingTime.lean` being **integrable**
  for every `ξ > 0` (Garivier & Kaufmann, Proposition 13),

Chernoff's stopping time satisfies, for every `δ ∈ (0, 1)` and almost every
trajectory,

  `τ_δ ≤ W + ⌈(1 + ε) c*(ν) log(1/δ)⌉`,   `E[W] < ∞`,

with `W` free of `δ`.  This is Garivier & Kaufmann's Theorem 14 and the upper
half of Lattimore & Szepesvári's Theorem 33.6.

## Where the constant comes from

Three multiplicative losses, each `(1 + θ)`, are incurred and no more:

1. the slope is taken at `r = 1/((1 + θ) c*)` rather than `1/c*`, because the
   window `ξ` has to be strictly positive (`Solutions/RateFromTracking.lean`);
2. `f⁻¹(δ) ≤ (1 + θ) log(1/δ) + C(k, θ)`
   (`Solutions/ChernoffInverseLinear.lean`);
3. the crossing round is `(1 + θ)β₀/r` rather than `β₀/r`, the extra `θ`-share of
   the line paying for the logarithmic term `k log(t² + t)`
   (`Solutions/CrossingSharp.lean`).

So the coefficient of `log(1/δ)` is `(1 + θ)³ c*`, and `θ = min(1, ε/7)` makes
`(1 + θ)³ ≤ 1 + 7θ ≤ 1 + ε`.  Every other cost is additive and `δ`-free, hence
joins `W`.

## Why the integrability hypothesis is not removable

Almost-sure convergence of the empirical allocation is *not* enough to make `W`
integrable, and in fact not enough for the conclusion to hold at all.  A sampling
rule may pull arm `1` for the first `M` rounds, where `M` is a function of the
first reward with `E[M] = ∞`; while `T_2(t) = 0` the statistic `Z_t` vanishes, so
`τ_δ ≥ M` and `E[τ_δ] = ∞`, yet the empirical allocation still converges almost
surely because `M < ∞` almost surely.  The quantitative input — here the
integrability of `T_ξ`, in Garivier & Kaufmann the forced exploration of
D-Tracking — is doing real work.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Topology

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-! ## The slack bookkeeping -/

/-- `θ = min(1, ε/7)` turns a triple `(1 + θ)` loss into a single `(1 + ε)`. -/
theorem cube_one_add_le {ε : ℝ} (hε : 0 < ε) :
    0 < min 1 (ε / 7) ∧ (1 + min 1 (ε / 7)) ^ 3 ≤ 1 + ε := by
  set θ : ℝ := min 1 (ε / 7) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (by positivity)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθε : 7 * θ ≤ ε := by
    have : θ ≤ ε / 7 := min_le_right _ _
    linarith
  refine ⟨hθ0, ?_⟩
  nlinarith [sq_nonneg θ, hθ0.le, hθ1]

/-! ## The theorem -/

/-- **Theorem 14 (Garivier–Kaufmann), conditionally on Proposition 13.**  If the
settling times are integrable, Chernoff's stopping time is bounded by a `δ`-free
integrable random time plus `⌈(1 + ε) c*(ν) log(1/δ)⌉`.

The hypothesis `hsettle` is exactly Proposition 13: for each accuracy `ξ` the
empirical allocation and means settle to within `ξ` almost surely, and the round
at which they do has finite expectation. -/
theorem chernoff_stopping_time_le_integrable_plus_linear_of_settling
    (pol : BanditPolicy k) (μvec : Fin k → ℝ) {istar : Fin k}
    (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hk2 : ∃ j : Fin k, j ≠ istar)
    (α : Fin k → ℝ≥0) (hαpos : ∀ i, 0 < α i)
    (hopt : IsOptimalAllocation (gaussianBandit μvec)
      (Set.range (gaussianBandit (k := k))) α)
    (hsettle : ∀ ξ : ℝ, 0 < ξ →
      (∀ᵐ ω ∂(banditTrajMeasure (gaussianBandit μvec) pol),
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ω ∈ settlingEvent (fun i ↦ (α i : ℝ)) μvec ξ n) ∧
        ∫⁻ ω, (settlingTime (fun i ↦ (α i : ℝ)) μvec ξ ω : ℝ≥0∞)
          ∂(banditTrajMeasure (gaussianBandit μvec) pol) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : (ℕ → Fin k × ℝ) → ℕ,
      (∫⁻ ω, (W ω : ℝ≥0∞) ∂(banditTrajMeasure (gaussianBandit μvec) pol) ≠ ⊤) ∧
        ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
          ∀ᵐ ω ∂(banditTrajMeasure (gaussianBandit μvec) pol),
            chernoffStoppingTime (k := k) δ ω
              ≤ ((W ω : ℕ∞) + ((⌈(1 + ε)
                  * baiComplexityReal (gaussianBandit μvec)
                      (Set.range (gaussianBandit (k := k)))
                  * Real.log (1 / δ)⌉₊ : ℕ) : ℕ∞)) := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  obtain ⟨j₀, hj₀⟩ := hk2
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure (gaussianBandit μvec) pol with hP
  -- the characteristic time as a positive real
  set c : ℝ := baiComplexityReal (gaussianBandit μvec)
    (Set.range (gaussianBandit (k := k))) with hc
  have hc0 : 0 < c := baiComplexityReal_pos hstar hαpos hopt hj₀
  -- the slack
  obtain ⟨hθ0, hθcube⟩ := cube_one_add_le hε
  set θ : ℝ := min 1 (ε / 7) with hθdef
  have hθ1 : (0 : ℝ) < 1 + θ := by linarith
  -- the slope
  set r : ℝ := 1 / ((1 + θ) * c) with hrdef
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hrinv : 1 / r = (1 + θ) * c := by
    rw [hrdef, one_div_one_div]
  have hαR : ∀ i, (0 : ℝ) < (α i : ℝ) := fun i ↦ by exact_mod_cast hαpos i
  -- the slope is strictly below every pair rate
  have hrate : ∀ j, j ≠ istar → r < pairRate (fun i ↦ (α i : ℝ)) μvec istar j := by
    intro j hj
    have hpc : c⁻¹ ≤ pairCost α μvec istar j :=
      inv_baiComplexityReal_le_pairCost hstar hαpos hopt hj
    have hlt : r < c⁻¹ := by
      rw [hrdef, one_div, inv_lt_inv₀ (by positivity) hc0]
      nlinarith
    calc r < c⁻¹ := hlt
      _ ≤ pairCost α μvec istar j := hpc
      _ = pairRate (fun i ↦ (α i : ℝ)) μvec istar j := rfl
  -- the window
  obtain ⟨ξ, hξ0, hξα, hξgap, hξrate⟩ := exists_window hαR hstar hrate
  obtain ⟨hae, hint⟩ := hsettle ξ hξ0
  -- the `δ`-free part
  set B : ℕ := ⌈(1 + θ) * chernoffInverseConst k θ / r⌉₊ with hB
  refine ⟨fun ω ↦ crossWitness k r θ ω + B, ?_, ?_⟩
  · -- integrability
    have hsplit : ∀ ω, ((crossWitness k r θ ω + B : ℕ) : ℝ≥0∞)
        = (crossWitness k r θ ω : ℝ≥0∞) + (B : ℝ≥0∞) := by
      intro ω; push_cast; ring
    rw [lintegral_congr hsplit, MeasureTheory.lintegral_add_right _ measurable_const,
      MeasureTheory.lintegral_const, measure_univ, mul_one]
    refine ENNReal.add_ne_top.mpr ⟨?_, ENNReal.natCast_ne_top _⟩
    refine ne_top_of_le_ne_top ?_ (lintegral_crossWitness_le (r := r) (ε := θ) P)
    refine ENNReal.add_ne_top.mpr ⟨?_, ENNReal.natCast_ne_top _⟩
    exact lintegral_eventuallyIn_glrLinearEvent_ne_top hξ0 hξα hξgap hξrate P hae hint
  · -- the bound
    intro δ hδ
    obtain ⟨hδ0, hδ1⟩ := hδ
    have hL : 0 ≤ Real.log (1 / δ) := by
      rw [one_div]
      exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ0, hδ1.le⟩)
    -- the coefficient of `log(1/δ)`
    have hA : (1 + θ) * (1 + θ) / r ≤ (1 + ε) * c := by
      have hid : (1 + θ) * (1 + θ) / r = (1 + θ) ^ 3 * c := by
        rw [hrdef]
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_right hθcube hc0.le
    have hceil : ⌈(1 + θ) * (1 + θ) / r * Real.log (1 / δ)⌉₊
        ≤ ⌈(1 + ε) * c * Real.log (1 / δ)⌉₊ :=
      Nat.ceil_mono (mul_le_mul_of_nonneg_right hA hL)
    filter_upwards [hae] with ω hω
    have hline : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ENNReal.ofReal (r * (n : ℝ)) ≤ trajGLR n ω :=
      exists_eventually_of_settles hξ0 hξα hξgap hξrate hω
    have hstop := chernoffStoppingTime_le_crossWitness_add (k := k) hk hr0 hθ0
      hδ0 hδ1.le hline
    refine le_trans hstop ?_
    have hbud : ⌈crossingBudget k r θ δ⌉₊
        ≤ ⌈(1 + θ) * (1 + θ) / r * Real.log (1 / δ)⌉₊ + B :=
      ceil_crossingBudget_le hk hr0 hθ0 hδ0 hδ1.le
    have hnat : crossWitness k r θ ω + ⌈crossingBudget k r θ δ⌉₊
        ≤ (crossWitness k r θ ω + B) + ⌈(1 + ε) * c * Real.log (1 / δ)⌉₊ := by
      omega
    calc ((crossWitness k r θ ω + ⌈crossingBudget k r θ δ⌉₊ : ℕ) : ℕ∞)
        ≤ (((crossWitness k r θ ω + B) + ⌈(1 + ε) * c * Real.log (1 / δ)⌉₊ : ℕ) : ℕ∞) := by
          exact_mod_cast Nat.cast_le.mpr hnat
      _ = ((crossWitness k r θ ω + B : ℕ) : ℕ∞)
            + ((⌈(1 + ε) * c * Real.log (1 / δ)⌉₊ : ℕ) : ℕ∞) := by push_cast; ring

end BanditAlgorithm

theorem _root_.solution
    {k : ℕ} [NeZero k] (pol : BanditAlgorithm.BanditPolicy k) (μvec : Fin k → ℝ)
    {istar : Fin k} (hstar : ∀ j, j ≠ istar → μvec j < μvec istar)
    (hk2 : ∃ j : Fin k, j ≠ istar)
    (α : Fin k → NNReal) (hαpos : ∀ i, 0 < α i)
    (hopt : BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
      (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α)
    (hsettle : ∀ ξ : ℝ, 0 < ξ →
      (∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol),
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))) ∧
        ∫⁻ ω, ((sInf {N : ℕ | ∀ n, N ≤ n →
            (0 < n ∧
              (∀ i, |BanditAlgorithm.trajAllocation i n ω - (α i : ℝ)| ≤ ξ) ∧
              (∀ i, |BanditAlgorithm.trajEmpiricalMean i n ω - μvec i| ≤ ξ))} : ℕ) : ℝ≥0∞)
          ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ W : (ℕ → Fin k × ℝ) → ℕ,
      (∫⁻ ω, (W ω : ℝ≥0∞)
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) ≠ ⊤) ∧
        ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
          ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol),
            BanditAlgorithm.chernoffStoppingTime (k := k) δ ω
              ≤ ((W ω : ℕ∞) + ((⌈(1 + ε)
                  * (BanditAlgorithm.baiComplexity (BanditAlgorithm.gaussianBandit μvec)
                      (Set.range (BanditAlgorithm.gaussianBandit (k := k)))).toReal
                  * Real.log (1 / δ)⌉₊ : ℕ) : ℕ∞)) :=
  BanditAlgorithm.chernoff_stopping_time_le_integrable_plus_linear_of_settling
    pol μvec hstar hk2 α hαpos hopt hsettle hε
