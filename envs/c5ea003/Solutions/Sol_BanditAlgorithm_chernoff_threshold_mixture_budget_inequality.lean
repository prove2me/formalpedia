-- Prove2me | solution 1 for BanditAlgorithm.chernoff_threshold_mixture_budget_inequality
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T22:03:26.661879+00:00
-- url     : https://prove2.me/submissions/daa2d507-c6a4-438b-b8c0-41d1784e09fc

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_TrackAndStop

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
# The threshold inequality

This is the quantitative step that turns the mixture martingale into the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7.

Running the pair mixture at prior variance `c` controls the statistic
`Z_i²/(2(T_i + 1/c))` at the price `½log(1+cT_i)` per arm, plus `log(1/δ')` where
`δ'` is the confidence budget of a single pair.  Converting that into a statement
about the true statistic `Z_i²/(2T_i)` at threshold `β_n(δ)` requires

  `(c/(c+1)) · (k log(n²+n) + β₀)  ≥  log(1/δ) + log(k(k−1)) + log(1+c/2) + log n`

for every `n ≥ 1`, where `β₀ = f⁻¹(δ)`: the factor `c/(c+1)` is the loss from the
shift `T ↦ T + 1/c`, the `log(k(k−1))` is the union over ordered pairs of arms, and
`log(1+c/2) + log n` bounds the two `½log(1+cT_i)` prices.

**The choice of variance is `c = β₀`.**  This is what makes the inequality true,
and it is not arbitrary: the loss `c/(c+1)` must be within `O(1/β₀)` of `1`
because the whole budget `log(1/δ)` passes through it, while the price
`½log(1+c)` must stay within the slack of `β₀` over `k + log(1/δ)`.  That slack is
`k log(β₀/k)` — the sharp lower bound of `Solutions/ChernoffInverseSharp.lean` —
and it grows like `k log log(1/δ)`, exactly matching `log c`.  Neither a bounded
`c` nor a `c` growing faster than polynomially in `β₀` works.

After substituting the sharp bound on `β₀` and clearing the denominator the
inequality reduces to `b·P + Q ≥ 0` where

  `P = k log 2 + k − 1 − 2 log k − log(k−1)`,   `Q = k − 2 log k − log(k−1)`,

and both `P ≥ 0` and `2P + Q ≥ 0` follow from `log x ≤ x/e` alone.
-/

open Real

namespace BanditAlgorithm

/-! ## The two elementary positivity facts -/

/-- `P ≥ 0`: the coefficient of `b` after clearing denominators. -/
theorem threshold_coeff_P_nonneg {k : ℕ} (hk2 : 2 ≤ k) :
    0 ≤ (k : ℝ) * Real.log 2 + (k : ℝ) - 1
        - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlkNN : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hlk1NN : 0 ≤ Real.log ((k : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hlk' : Real.log (k : ℝ) * 2.7182818283 ≤ (k : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlkNN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk0))
  have hlk1' : Real.log ((k : ℝ) - 1) * 2.7182818283 ≤ (k : ℝ) - 1 :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlk1NN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk10))
  have hkL2 : (0.6931471803 : ℝ) * (k : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hl2.le hk0.le
  linarith [hlk', hlk1', hkL2, hkR]

/-- `2P + Q ≥ 0`: the value at the smallest admissible `b = 2`. -/
theorem threshold_coeff_PQ_nonneg {k : ℕ} (hk2 : 2 ≤ k) :
    0 ≤ 2 * ((k : ℝ) * Real.log 2 + (k : ℝ) - 1
          - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1))
        + ((k : ℝ) - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1)) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlkNN : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hlk1NN : 0 ≤ Real.log ((k : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hlk' : Real.log (k : ℝ) * 2.7182818283 ≤ (k : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlkNN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk0))
  have hlk1' : Real.log ((k : ℝ) - 1) * 2.7182818283 ≤ (k : ℝ) - 1 :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlk1NN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk10))
  have hkL2 : (0.6931471803 : ℝ) * (k : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hl2.le hk0.le
  linarith [hlk', hlk1', hkL2, hkR]

/-! ## The threshold inequality -/

/-- **The threshold inequality.**  With the prior variance set to `b = f⁻¹(δ)`, the
mixture budget covers the Chernoff threshold at every round `n ≥ 1`. -/
theorem threshold_master {k : ℕ} (hk2 : 2 ≤ k) {b L : ℝ} (hbk : (k : ℝ) ≤ b)
    (hL0 : 0 ≤ L) (hLb : (k : ℝ) + L + (k : ℝ) * Real.log (b / (k : ℝ)) ≤ b)
    {n : ℕ} (hn : 1 ≤ n) :
    L + Real.log ((k : ℝ) * ((k : ℝ) - 1)) + Real.log (1 + b / 2) + Real.log (n : ℝ)
      ≤ b / (b + 1) * ((k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + b) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hb2 : (2 : ℝ) ≤ b := le_trans hkR hbk
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (0 : ℝ) < b + 1 := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- the logarithms appearing
  have hA : Real.log ((n : ℝ) ^ 2 + (n : ℝ))
      = Real.log (n : ℝ) + Real.log ((n : ℝ) + 1) := by
    rw [show (n : ℝ) ^ 2 + (n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) by ring,
      Real.log_mul hn0.ne' (by linarith)]
  have hkk : Real.log ((k : ℝ) * ((k : ℝ) - 1))
      = Real.log (k : ℝ) + Real.log ((k : ℝ) - 1) := Real.log_mul hk0.ne' hk10.ne'
  have hbdiv : Real.log (b / (k : ℝ)) = Real.log b - Real.log (k : ℝ) :=
    Real.log_div hb0.ne' hk0.ne'
  have hhalf : Real.log (1 + b / 2) ≤ Real.log b :=
    Real.log_le_log (by linarith) (by linarith)
  have hLn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hLn1 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLbk : Real.log (k : ℝ) ≤ Real.log b := Real.log_le_log hk0 hbk
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the two positivity facts
  have hP := threshold_coeff_P_nonneg hk2
  have hPQ := threshold_coeff_PQ_nonneg hk2
  -- clear the denominator
  rw [div_mul_eq_mul_div, le_div_iff₀ hb1]
  rw [hkk, hA]
  -- the bound on `L`
  have hLub : L ≤ b - (k : ℝ) - (k : ℝ) * (Real.log b - Real.log (k : ℝ)) := by
    rw [hbdiv] at hLb
    linarith
  -- the leading `log n` coefficient is nonnegative
  have hcoefn : 0 ≤ (b * (k : ℝ) - b - 1) * Real.log (n : ℝ) := by
    have : (0 : ℝ) ≤ b * (k : ℝ) - b - 1 := by nlinarith
    exact mul_nonneg this hLn0
  -- the `log(n+1)` term dominates `log 2`
  have hcoefn1 : b * (k : ℝ) * Real.log 2 ≤ b * (k : ℝ) * Real.log ((n : ℝ) + 1) := by
    have hbk0 : (0 : ℝ) ≤ b * (k : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hLn1 hbk0
  -- `log b ≥ log k`, weighted
  have hcoefb : (b + 1) * ((k : ℝ) - 1) * Real.log (k : ℝ)
      ≤ (b + 1) * ((k : ℝ) - 1) * Real.log b := by
    have : (0 : ℝ) ≤ (b + 1) * ((k : ℝ) - 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left hLbk this
  -- `b · P ≥ 2 · P`
  have hbP : 2 * ((k : ℝ) * Real.log 2 + (k : ℝ) - 1
        - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1))
      ≤ b * ((k : ℝ) * Real.log 2 + (k : ℝ) - 1
        - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1)) := by
    nlinarith [hP, hb2]
  nlinarith [hLub, hcoefn, hcoefn1, hcoefb, hbP, hPQ, hhalf, hb1, hb2, hLn0, hL2pos]

end BanditAlgorithm

theorem _root_.solution {k : ℕ} (hk2 : 2 ≤ k) {b L : ℝ} (hbk : (k : ℝ) ≤ b)
    (hL0 : 0 ≤ L) (hLb : (k : ℝ) + L + (k : ℝ) * Real.log (b / (k : ℝ)) ≤ b)
    {n : ℕ} (hn : 1 ≤ n) :
    L + Real.log ((k : ℝ) * ((k : ℝ) - 1)) + Real.log (1 + b / 2) + Real.log (n : ℝ)
      ≤ b / (b + 1) * ((k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + b) :=
  BanditAlgorithm.threshold_master hk2 hbk hL0 hLb hn
