-- Prove2me | solution 1 for BanditAlgorithm.chernoff_glr_never_favours_suboptimal_arm
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T19:43:24.171548+00:00
-- url     : https://prove2.me/submissions/ee5a33a6-6615-4fb0-870e-f706a4a959cf

import Theorems.Thm_BanditAlgorithm_chernoff_pairwise_selfnormalised_deviation_bound
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Exp


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
# Reducing the soundness of Chernoff's rule to a self-normalised deviation bound

The first step of the proof of L&S Lemma 33.7 is purely algebraic, and this file
carries it out.  Suppose that in round `n`

* the GLR statistic has crossed its (strictly positive) threshold,
  `β_n(δ) ≤ Z_n`, and
* the empirical maximum is attained at an arm `i` which is *not* optimal.

Pick any arm `j` with `μ_i < μ_j`.  Then:

* the empirical maximiser is unique — otherwise `Z_n = 0 < β_n(δ)` — so it is `i`,
  and hence `Z_n ≤ ½ T_i T_j/(T_i + T_j) (μ̂_i − μ̂_j)²`;
* both `T_i` and `T_j` are positive, since otherwise that pair term vanishes;
* the empirical order `μ̂_j ≤ μ̂_i` is the *reverse* of the true order `μ_i < μ_j`,
  so the pooled-mean inequality `pq/(p+q)(u−v)² ≤ p(u−x)² + q(v−y)²`
  (valid whenever `v ≤ u` and `x ≤ y`) applies with
  `u = μ̂_i, v = μ̂_j, x = μ_i, y = μ_j`.

The conclusion is that the *self-normalised deviation* of the pair `(i, j)` from
the true means already exceeds `β_n(δ)`:

  `β_n(δ) ≤ ½ T_i (μ̂_i − μ_i)² + ½ T_j (μ̂_j − μ_j)²`.

Everything probabilistic is thereby isolated into a bound on that event, which is
the classical Chernoff-plus-union-bound-over-pull-counts estimate.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ} [NeZero k]

/-- The self-normalised pair deviation from the true means. -/
noncomputable def pairDeviation (μvec : Fin k → ℝ) (a b : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  (trajPullCount a n ω : ℝ) * ((trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
    + (trajPullCount b n ω : ℝ) * ((trajEmpiricalMean b n ω - μvec b) ^ 2 / 2)

/-- **The algebraic step of L&S Lemma 33.7.** -/
theorem exists_pairDeviation_ge {μvec : Fin k → ℝ} {n : ℕ} {ω : ℕ → Fin k × ℝ}
    {i : Fin k} {β : ℝ} (hβ : 0 < β)
    (hfire : ENNReal.ofReal β ≤ trajGLR n ω)
    (hmax : ∀ j, trajEmpiricalMean j n ω ≤ trajEmpiricalMean i n ω)
    (hsub : 0 < banditGap (gaussianBandit μvec) i) :
    ∃ a b : Fin k, a ≠ b ∧ β ≤ pairDeviation μvec a b n ω := by
  classical
  -- `i` is a strictly suboptimal arm, so some arm beats it
  obtain ⟨j, hj⟩ := (banditGap_pos_iff μvec i).mp hsub
  have hji : j ≠ i := by
    rintro rfl
    exact absurd hj (lt_irrefl _)
  -- the threshold is positive, so `Z_n ≠ 0` and the empirical maximiser is unique
  have hZne : trajGLR n ω ≠ 0 := by
    intro h0
    rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hfire
    exact absurd hfire (not_le.mpr hβ)
  have hieq : i = trajArgmax n ω := by
    by_contra hne
    exact hZne (trajGLR_eq_zero_of_not_unique n ω hne hmax)
  -- so `Z_n` is at most the `(i, j)` pair term
  have hle : trajGLR n ω ≤ ENNReal.ofReal (trajPairGLR i j n ω) := by
    rw [trajGLR_eq_at_argmax, ← hieq]
    exact le_trans (iInf_le _ j) (iInf_le _ hji)
  have hβle : β ≤ trajPairGLR i j n ω := by
    have h := le_trans hfire hle
    rwa [ENNReal.ofReal_le_ofReal_iff (trajPairGLR_nonneg i j n ω)] at h
  -- both arms must have been played
  have hTi : (0 : ℝ) < (trajPullCount i n ω : ℝ) := by
    rcases Nat.eq_zero_or_pos (trajPullCount i n ω) with h0 | hpos
    · exfalso
      rw [trajPairGLR, h0] at hβle
      simp at hβle
      linarith
    · exact_mod_cast hpos
  have hTj : (0 : ℝ) < (trajPullCount j n ω : ℝ) := by
    rcases Nat.eq_zero_or_pos (trajPullCount j n ω) with h0 | hpos
    · exfalso
      rw [trajPairGLR, h0] at hβle
      simp at hβle
      linarith
    · exact_mod_cast hpos
  -- the empirical order is the reverse of the true order: apply the pooled bound
  refine ⟨i, j, Ne.symm hji, ?_⟩
  have hpooled : trajPairGLR i j n ω ≤ pairDeviation μvec i j n ω := by
    have := pooled_le_of_crossed (p := (trajPullCount i n ω : ℝ))
      (q := (trajPullCount j n ω : ℝ)) (u := trajEmpiricalMean i n ω)
      (v := trajEmpiricalMean j n ω) (x := μvec i) (y := μvec j)
      hTi hTj (hmax j) hj.le
    simpa [trajPairGLR, pairDeviation] using this
  linarith

/-- The soundness event of Chernoff's rule is contained in the pairwise deviation
event. -/
theorem chernoff_event_subset (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (μvec : Fin k → ℝ) :
    {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ i : Fin k,
        ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω ∧
          (∀ j, trajEmpiricalMean j n ω ≤ trajEmpiricalMean i n ω) ∧
            0 < banditGap (gaussianBandit μvec) i}
      ⊆ {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ a b : Fin k, a ≠ b ∧
          chernoffThreshold k δ n ≤ pairDeviation μvec a b n ω} := by
  rintro ω ⟨n, i, hfire, hmax, hsub⟩
  obtain ⟨a, b, hab, hle⟩ :=
    exists_pairDeviation_ge (chernoffThreshold_pos hk hδ n) hfire hmax hsub
  exact ⟨n, a, b, hab, hle⟩

end BanditAlgorithm


theorem _root_.solution {k : ℕ} [NeZero k]
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (pol : BanditAlgorithm.BanditPolicy k)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν ∈ Set.range (BanditAlgorithm.gaussianBandit (k := k))) :
    BanditAlgorithm.banditTrajMeasure ν pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ i : Fin k,
          ENNReal.ofReal (BanditAlgorithm.chernoffThreshold k δ n)
              ≤ BanditAlgorithm.trajGLR n ω ∧
            (∀ j, BanditAlgorithm.trajEmpiricalMean j n ω
                ≤ BanditAlgorithm.trajEmpiricalMean i n ω) ∧
              0 < BanditAlgorithm.banditGap ν i}
      ≤ ENNReal.ofReal δ := by
  obtain ⟨μvec, rfl⟩ := hν
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  refine le_trans (measure_mono
    (BanditAlgorithm.chernoff_event_subset hk hδ.1 μvec)) ?_
  exact BanditAlgorithm.chernoff_pairwise_selfnormalised_deviation_bound δ hδ pol μvec
