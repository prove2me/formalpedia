-- Prove2me | solution 1 for BanditAlgorithm.klucb_selected_overshoot_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:53:24.79962+00:00
-- url     : https://prove2.me/submissions/9dc8a9da-4b4a-4bdf-85fc-8146408a04bb

import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail_half
import Theorems.Thm_BanditAlgorithm_bernoulliBandit_isSubgaussian_half
import Theorems.Thm_BanditAlgorithm_bernoulliRelativeEntropy_antitone_fst
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
import Theorems.Thm_BanditAlgorithm_klucb_index_threshold_feasible
import Definitions.Def_klucbFeasibilityFailureCount
import Definitions.Def_klucbFailureCount
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.Complex.ExponentialBounds

/-
The closed helper block below is reproduced unchanged from Harry_Xu's accepted
Prove2Me submission 1ebc4461-4a9e-4996-b6fb-fa7ac2175878 for theorem
d3ba2b23-aaff-45f3-aebc-080e1d80ddd7. It supplies adaptive Bernoulli rank
counting and the feasibility-count estimate. The new proof below connects the
registered KL-index count to that estimate; no private imported helper is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator_over {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    (armPullCount i h : ℝ) =
      ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hs : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hs]
  simpa using
    (Finset.sum_boole (R := ℝ)
      (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

private theorem measurable_armPullCount_over {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  simp_rw [pullCount_cast_eq_sum_indicator_over]
  apply Finset.measurable_sum
  intro t ht
  have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite
    ((measurableSet_singleton i).preimage hcoord)
    measurable_const measurable_const

private theorem armPullCount_snoc_over {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add, pullCount_cast_eq_sum_indicator_over,
    pullCount_cast_eq_sum_indicator_over i h, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armPullCount_le_horizon_over {k n : ℕ}
    (i : Fin k) (h : BanditHistory k n) :
    armPullCount i h ≤ n := by
  rw [armPullCount]
  calc
    {t | (h t).1 = i}.toFinset.card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := Fintype.card_fin n

private theorem measurable_armEmpiricalMean_over {k m : ℕ} (i : Fin k) :
    Measurable (armEmpiricalMean (n := m) i) := by
  have hsum :
      (fun h : BanditHistory k m ↦
        ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) =
      fun h ↦ ∑ t, if (h t).1 = i then (h t).2 else 0 := by
    funext h
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs, Finset.sum_filter]
  have hnum : Measurable
      (fun h : BanditHistory k m ↦
        ∑ t ∈ {t | (h t).1 = i}.toFinset, (h t).2) := by
    rw [hsum]
    apply Finset.measurable_sum
    intro t ht
    have ha : Measurable (fun h : BanditHistory k m ↦ (h t).1) :=
      measurable_fst.comp (measurable_pi_apply t)
    have hx : Measurable (fun h : BanditHistory k m ↦ (h t).2) :=
      measurable_snd.comp (measurable_pi_apply t)
    exact Measurable.ite ((measurableSet_singleton i).preimage ha)
      hx measurable_const
  unfold armEmpiricalMean
  exact hnum.div (measurable_armPullCount_over i)

private theorem measurable_banditHistoryPrefixAt_over
    {k n : ℕ} (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem measurable_armStoppedCenteredSum_over {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable (fun h : BanditHistory k (m + 1) ↦
          (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_over i).comp hinit
      have hlt : MeasurableSet {h : BanditHistory k (m + 1) |
          armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet {h : BanditHistory k (m + 1) |
          (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

private theorem prefixAt_snoc_castSucc_over {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) r.castSucc =
      banditHistoryPrefixAt h r := by
  funext s
  unfold banditHistoryPrefixAt
  have hsr : s.val < r.val := by simpa using s.isLt
  have hsn : s.val < n := lt_trans hsr r.isLt
  rw [Fin.snoc]
  rw [dif_pos hsn]
  simp

private theorem prefixAt_snoc_last_over {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem armStoppedCenteredSum_snoc_over {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

private noncomputable def armCenteredSumOver {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

private theorem armCenteredSumOver_snoc {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armCenteredSumOver ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSumOver ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSumOver, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem armStoppedCenteredSum_eq_pullCount_mul_over
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  classical
  have hstop :
      armStoppedCenteredSum ν i u m h = armCenteredSumOver ν i h := by
    induction m with
    | zero => simp [armStoppedCenteredSum, armCenteredSumOver]
    | succ m ih =>
        rw [← Fin.snoc_init_self h] at hcount ⊢
        rw [armPullCount_snoc_over] at hcount
        rw [armStoppedCenteredSum_snoc_over, armCenteredSumOver_snoc]
        by_cases hi : (h (Fin.last m)).1 = i
        · have hprev : armPullCount i (Fin.init h) < u := by
            simp [hi] at hcount
            omega
          rw [if_pos ⟨hprev, hi⟩, if_pos hi,
            ih (Fin.init h) (Nat.le_of_lt hprev)]
        · have hprev : armPullCount i (Fin.init h) ≤ u := by
            simpa [hi] using hcount
          rw [if_neg (fun hc ↦ hi hc.2), if_neg hi,
            ih (Fin.init h) hprev]
  rw [hstop]
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSumOver, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

private theorem armPullCount_prefix_le_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n) (r : Fin n) :
    armPullCount i (banditHistoryPrefixAt h r) ≤ armPullCount i h := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [← Fin.snoc_init_self h]
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · rw [prefixAt_snoc_last_over, armPullCount_snoc_over]
        by_cases hz : (h (Fin.last n)).1 = i <;> simp [hz]
      · rw [prefixAt_snoc_castSucc_over, armPullCount_snoc_over]
        exact (ih (Fin.init h) s).trans
          (Nat.le_add_right _ _)

private theorem armStoppedCenteredSum_stable_after_prefix_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (h : BanditHistory k n) (r : Fin n) (u : ℕ)
    (hcount : armPullCount i (banditHistoryPrefixAt h r) = u) :
    armStoppedCenteredSum ν i u n h =
      armStoppedCenteredSum ν i u r.val (banditHistoryPrefixAt h r) := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [← Fin.snoc_init_self h] at hcount ⊢
      revert hcount
      refine Fin.lastCases ?_ (fun s hcount ↦ ?_) r
      · intro hcount
        rw [prefixAt_snoc_last_over] at hcount ⊢
        rw [armStoppedCenteredSum_snoc_over]
        rw [if_neg (by
          intro hc
          exact Nat.ne_of_lt hc.1 hcount)]
        simp
      · rw [prefixAt_snoc_castSucc_over] at hcount ⊢
        rw [armStoppedCenteredSum_snoc_over]
        have hprefix_le :
            u ≤ armPullCount i (Fin.init h) := by
          rw [← hcount]
          exact armPullCount_prefix_le_over i (Fin.init h) s
        rw [if_neg (by
          intro hc
          omega)]
        simpa using ih (Fin.init h) s hcount

private theorem prefixAt_prefixAt_over
    {k n : ℕ} (h : BanditHistory k n) (s : Fin n)
    (r : Fin s.val) :
    banditHistoryPrefixAt (banditHistoryPrefixAt h s) r =
      banditHistoryPrefixAt h
        (⟨r.val, lt_trans r.isLt s.isLt⟩ : Fin n) := by
  funext q
  rfl

private theorem selected_prefix_count_lt_total_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n) (r : Fin n)
    (hselected : (h r).1 = i) :
    armPullCount i (banditHistoryPrefixAt h r) < armPullCount i h := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      rw [← Fin.snoc_init_self h] at hselected ⊢
      revert hselected
      refine Fin.lastCases ?_ (fun s hselected ↦ ?_) r
      · intro hselected
        rw [prefixAt_snoc_last_over, armPullCount_snoc_over]
        simp only [Fin.snoc_last] at hselected
        simp [hselected]
      · rw [prefixAt_snoc_castSucc_over, armPullCount_snoc_over]
        have hselected' : ((Fin.init h) s).1 = i := by
          simpa using hselected
        exact (ih (Fin.init h) s hselected').trans_le (by omega)

private theorem selected_prefix_count_strict_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (r s : Fin n) (hrs : r.val < s.val)
    (hselected : (h r).1 = i) :
    armPullCount i (banditHistoryPrefixAt h r) <
      armPullCount i (banditHistoryPrefixAt h s) := by
  let r' : Fin s.val := ⟨r.val, hrs⟩
  have hsel' : ((banditHistoryPrefixAt h s) r').1 = i := by
    exact hselected
  have hlt :=
    selected_prefix_count_lt_total_over i (banditHistoryPrefixAt h s) r' hsel'
  simpa [r', prefixAt_prefixAt_over] using hlt

private theorem selected_prefix_count_injOn_over
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (R : Finset (Fin n))
    (hR : ∀ r ∈ R, (h r).1 = i) :
    Set.InjOn
      (fun r : Fin n ↦ armPullCount i (banditHistoryPrefixAt h r)) R := by
  intro r hr s hs heq
  rcases lt_trichotomy r.val s.val with hrs | hrs | hrs
  · have hlt := selected_prefix_count_strict_over i h r s hrs (hR r hr)
    exact (Nat.ne_of_lt hlt heq).elim
  · exact Fin.ext hrs
  · have hlt := selected_prefix_count_strict_over i h s r hrs (hR s hs)
    exact (Nat.ne_of_lt hlt heq.symm).elim

private theorem banditArmMean_bernoulli_over
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (j : Fin k) :
    banditArmMean ν j = μvec j := by
  rw [hν, banditArmMean, bernoulliBandit]
  change (∫ x : ℝ, x ∂(ENNReal.ofReal (μvec j) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - μvec j) • Measure.dirac (0 : ℝ))) = μvec j
  rw [integral_add_measure
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (1 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)]
  rcases hμ j with ⟨h0, h1⟩
  simp [ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - μvec j by linarith)]

private def HistoryRewardsBernoulliOver {k n : ℕ}
    (h : BanditHistory k n) : Prop :=
  ∀ t, (h t).2 = 0 ∨ (h t).2 = 1

private theorem empiricalMean_mem_Icc_over
    {k n : ℕ} (j : Fin k) (h : BanditHistory k n)
    (hh : HistoryRewardsBernoulliOver h) :
    armEmpiricalMean j h ∈ Set.Icc (0 : ℝ) 1 := by
  let S : Finset (Fin n) := {t | (h t).1 = j}.toFinset
  have hreward (t : Fin n) : 0 ≤ (h t).2 ∧ (h t).2 ≤ 1 := by
    rcases hh t with ht | ht <;> simp [ht]
  have hnum0 : 0 ≤ ∑ t ∈ S, (h t).2 :=
    Finset.sum_nonneg fun t _ ↦ (hreward t).1
  have hnumle : (∑ t ∈ S, (h t).2) ≤ (S.card : ℝ) := by
    calc
      (∑ t ∈ S, (h t).2) ≤ ∑ _t ∈ S, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ ↦ (hreward t).2
      _ = (S.card : ℝ) := by simp
  unfold armEmpiricalMean
  change (∑ t ∈ S, (h t).2) / (S.card : ℝ) ∈ Set.Icc (0 : ℝ) 1
  by_cases hc : S.card = 0
  · simp [hc]
  · have hcpos : 0 < (S.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hc
    exact ⟨div_nonneg hnum0 hcpos.le, (div_le_one hcpos).2 hnumle⟩

private theorem historyRewardsBernoulliOver_prefix
    {k n : ℕ} (h : BanditHistory k n)
    (hh : HistoryRewardsBernoulliOver h) (r : Fin n) :
    HistoryRewardsBernoulliOver (banditHistoryPrefixAt h r) := by
  intro t
  exact hh ⟨t.val, lt_trans t.isLt r.isLt⟩

private theorem bernoulli_arm_ae_reward_over
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (j : Fin k) :
    ∀ᵐ x ∂ν.P j, x = 0 ∨ x = 1 := by
  rw [hν, bernoulliBandit]
  change ∀ᵐ x ∂(ENNReal.ofReal (μvec j) • Measure.dirac (1 : ℝ) +
      ENNReal.ofReal (1 - μvec j) • Measure.dirac (0 : ℝ)),
    x = 0 ∨ x = 1
  rw [MeasureTheory.ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact Measure.ae_smul_measure (by simp) _

private theorem banditStepKernel_ae_reward_bernoulli_over
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.2 = 0 ∨ z.2 = 1 := by
  rw [banditStepKernel]
  apply Kernel.ae_compProd_of_ae_ae
  · exact (measurableSet_eq_fun measurable_snd measurable_const).union
      (measurableSet_eq_fun measurable_snd measurable_const)
  · filter_upwards with j
    rw [Kernel.comap_apply]
    exact bernoulli_arm_ae_reward_over μvec hμ ν hν j

private theorem measurableSet_historyRewardsBernoulliOver
    {k n : ℕ} :
    MeasurableSet {h : BanditHistory k n |
      HistoryRewardsBernoulliOver h} := by
  classical
  unfold HistoryRewardsBernoulliOver
  convert MeasurableSet.iInter (fun t : Fin n ↦
    (measurableSet_eq_fun
      (measurable_snd.comp (measurable_pi_apply t))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (0 : ℝ)))).union
    (measurableSet_eq_fun
      (measurable_snd.comp (measurable_pi_apply t))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (1 : ℝ))))) using 1
  ext h
  simp

private theorem banditMeasure_ae_historyRewardsBernoulliOver
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) :
    ∀ n : ℕ, ∀ᵐ h ∂banditMeasure ν π n,
      HistoryRewardsBernoulliOver h := by
  intro n
  induction n with
  | zero => simp [banditMeasure, HistoryRewardsBernoulliOver]
  | succ n ih =>
      rw [banditMeasure]
      apply (ae_map_iff measurable_banditHistorySnoc.aemeasurable
        (measurableSet_historyRewardsBernoulliOver
          (k := k) (n := n + 1))).2
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc
          (measurableSet_historyRewardsBernoulliOver
            (k := k) (n := n + 1))
      filter_upwards [ih] with h hh
      filter_upwards
        [banditStepKernel_ae_reward_bernoulli_over
          μvec hμ ν hν π h] with z hz
      intro t
      refine Fin.lastCases ?_ (fun s ↦ ?_) t
      · simpa using hz
      · simpa using hh s

private theorem klucbExploration_pos_over (t : ℕ) :
    0 < klucbExploration t := by
  rw [klucbExploration]
  nlinarith [mul_nonneg (Nat.cast_nonneg t)
    (sq_nonneg (Real.log t))]

private theorem klucbExploration_mono_over
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    klucbExploration s ≤ klucbExploration t := by
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have htR : (1 : ℝ) ≤ t := hsR.trans (by exact_mod_cast hst)
  have hstR : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hlog :
      Real.log (s : ℝ) ≤ Real.log (t : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (lt_of_lt_of_le zero_lt_one hsR)
      (lt_of_lt_of_le zero_lt_one htR) hstR
  have hlogs : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hsR
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg htR
  have hsq :
      Real.log (s : ℝ) ^ 2 ≤ Real.log (t : ℝ) ^ 2 := by
    nlinarith
  have hprod :
      (s : ℝ) * Real.log (s : ℝ) ^ 2 ≤
        (t : ℝ) * Real.log (t : ℝ) ^ 2 :=
    mul_le_mul hstR hsq (sq_nonneg _) (Nat.cast_nonneg _)
  simpa only [klucbExploration, add_comm] using add_le_add_left hprod 1

private theorem log_klucbExploration_mono_over
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Real.log (klucbExploration s) ≤ Real.log (klucbExploration t) :=
  Real.strictMonoOn_log.monotoneOn
    (klucbExploration_pos_over s)
    (klucbExploration_pos_over t)
    (klucbExploration_mono_over hs hst)

private noncomputable def klOvershootTailIndicatorOver
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) (h : BanditHistory k n) : ℝ :=
  if (u : ℝ) * ε ≤ armStoppedCenteredSum ν i u n h then 1 else 0

private theorem measurable_klOvershootTailIndicator_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) :
    Measurable (klOvershootTailIndicatorOver ν i ε u :
      BanditHistory k n → ℝ) := by
  unfold klOvershootTailIndicatorOver
  exact Measurable.ite
    (measurableSet_le measurable_const
      (measurable_armStoppedCenteredSum_over ν i u n))
    measurable_const measurable_const

private theorem integrable_klOvershootTailIndicator_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ) :
    Integrable (klOvershootTailIndicatorOver ν i ε u)
      (banditMeasure ν π n) := by
  apply Integrable.of_bound
    (measurable_klOvershootTailIndicator_over ν i ε u).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun h ↦ by
    unfold klOvershootTailIndicatorOver
    split <;> norm_num

private theorem integral_klOvershootTailIndicator_eq_probability_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ) :
    (∫ h, klOvershootTailIndicatorOver ν i ε u h
        ∂banditMeasure ν π n) =
      (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * ε ≤ armStoppedCenteredSum ν i u n h} := by
  let E : Set (BanditHistory k n) :=
    {h | (u : ℝ) * ε ≤ armStoppedCenteredSum ν i u n h}
  have hE : MeasurableSet E :=
    measurableSet_le measurable_const
      (measurable_armStoppedCenteredSum_over ν i u n)
  have hfun :
      (klOvershootTailIndicatorOver ν i ε u :
        BanditHistory k n → ℝ) =
        E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext h
    unfold klOvershootTailIndicatorOver
    change (if h ∈ E then (1 : ℝ) else 0) =
      E.indicator (fun _ ↦ (1 : ℝ)) h
    by_cases hh : h ∈ E <;> simp [Set.indicator, hh]
  rw [hfun]
  exact integral_indicator_one hE

private theorem integral_klOvershootTailIndicator_le_over
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν)
    (π : BanditPolicy k) (i : Fin k) (ε : ℝ) (u : ℕ)
    (hε : 0 < ε) :
    (∫ h, klOvershootTailIndicatorOver ν i ε u h
        ∂banditMeasure ν π n) ≤
      Real.exp (-2 * (u : ℝ) * ε ^ 2) := by
  rw [integral_klOvershootTailIndicator_eq_probability_over]
  exact
    (bandit_adaptive_stopped_centered_sum_tail_half
      (n := n) (π := π) ν hν i u hε.le).1

private theorem feasible_event_implies_small_or_empirical_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (q p₀ A D : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1)
    (hp₀q : p₀ < q)
    (hD : D = bernoulliRelativeEntropy p₀ q)
    (hDpos : 0 < D)
    (h : BanditHistory k n) (hh : HistoryRewardsBernoulliOver h)
    (r : Fin n)
    (hinit :
      ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0)
    (hfeas :
      klucbTruncatedRelativeEntropy
          (armEmpiricalMean i (banditHistoryPrefixAt h r)) q ≤
        Real.log (klucbExploration (r.val + 1)) /
          armPullCount i (banditHistoryPrefixAt h r))
    (hAmono : Real.log (klucbExploration (r.val + 1)) ≤ A) :
    (armPullCount i (banditHistoryPrefixAt h r) : ℝ) ≤ A / D ∨
      p₀ ≤ armEmpiricalMean i (banditHistoryPrefixAt h r) := by
  let u : ℕ := armPullCount i (banditHistoryPrefixAt h r)
  let p : ℝ := armEmpiricalMean i (banditHistoryPrefixAt h r)
  have hu0 : 0 < (u : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (hinit i)
  by_cases hsmall : (u : ℝ) ≤ A / D
  · exact Or.inl hsmall
  · right
    have hlarge : A / D < (u : ℝ) := lt_of_not_ge hsmall
    have hpIcc : p ∈ Set.Icc (0 : ℝ) 1 :=
      empiricalMean_mem_Icc_over i (banditHistoryPrefixAt h r)
        (historyRewardsBernoulliOver_prefix h hh r)
    by_cases hpq : p ≤ q
    · by_contra hnot
      have hpp₀ : p < p₀ := lt_of_not_ge hnot
      have hmono :
          D ≤ bernoulliRelativeEntropy p q := by
        rw [hD]
        exact bernoulliRelativeEntropy_antitone_fst
          hpIcc hpp₀.le hp₀q.le hq
      have htrunc :
          klucbTruncatedRelativeEntropy p q =
            bernoulliRelativeEntropy p q := by
        rw [klucbTruncatedRelativeEntropy, if_pos hpq]
      have hdle :
          bernoulliRelativeEntropy p q ≤
            Real.log (klucbExploration (r.val + 1)) / (u : ℝ) := by
        simpa [p, u, htrunc] using hfeas
      have hbudget :
          Real.log (klucbExploration (r.val + 1)) / (u : ℝ) ≤
            A / (u : ℝ) :=
        div_le_div_of_nonneg_right hAmono hu0.le
      have huD : (u : ℝ) * D ≤ A := by
        have hDA : D ≤ A / (u : ℝ) :=
          hmono.trans (hdle.trans hbudget)
        have := (le_div_iff₀ hu0).mp hDA
        simpa [mul_comm] using this
      have hAD : A < (u : ℝ) * D := by
        rwa [div_lt_iff₀ hDpos] at hlarge
      linarith
    · exact hp₀q.le.trans (lt_of_not_ge hpq).le

private theorem sum_small_or_tail_le_over
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (tail : ℕ → ℝ) (htail : ∀ u, 0 ≤ tail u) :
    (∑ u ∈ Finset.Icc 1 n,
        if (u : ℝ) ≤ x then (1 : ℝ) else tail u) ≤
      x + ∑ u ∈ Finset.Icc 1 n, tail u := by
  classical
  let S : Finset ℕ :=
    (Finset.Icc 1 n).filter fun u ↦ (u : ℝ) ≤ x
  have hSsubset : S ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro u hu
    have hu' := Finset.mem_filter.mp hu
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hu'.1).1, Nat.le_floor hu'.2⟩
  have hcardNat : S.card ≤ ⌊x⌋₊ := by
    calc
      S.card ≤ (Finset.Icc 1 ⌊x⌋₊).card :=
        Finset.card_le_card hSsubset
      _ = ⌊x⌋₊ := by simp [Nat.card_Icc]
  have hcard : (S.card : ℝ) ≤ x := by
    have hcast : (S.card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast hcardNat
    exact hcast.trans (Nat.floor_le hx)
  calc
    (∑ u ∈ Finset.Icc 1 n,
        if (u : ℝ) ≤ x then (1 : ℝ) else tail u) ≤
      (∑ u ∈ Finset.Icc 1 n,
        if (u : ℝ) ≤ x then (1 : ℝ) else 0) +
        ∑ u ∈ Finset.Icc 1 n, tail u := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro u hu
      by_cases hux : (u : ℝ) ≤ x
      · simp [hux, htail u]
      · simp [hux, htail u]
    _ = (S.card : ℝ) + ∑ u ∈ Finset.Icc 1 n, tail u := by
      rw [Finset.sum_boole]
    _ ≤ x + ∑ u ∈ Finset.Icc 1 n, tail u := by
      gcongr

private theorem feasibilityCount_snd_le_budget_add_tail_over
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (a i : Fin k) (ε₁ ε₂ : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hgap : 0 < banditGap ν i)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hεsum : ε₁ + ε₂ < banditGap ν i)
    (h : BanditHistory k n) (hh : HistoryRewardsBernoulliOver h) :
    (klucbFeasibilityFailureCount ν a i ε₂ h).2 ≤
      Real.log (klucbExploration n) /
          bernoulliRelativeEntropy
            (banditArmMean ν i + ε₁)
            (banditOptimalMean ν - ε₂) +
        ∑ u ∈ Finset.Icc 1 n,
          klOvershootTailIndicatorOver ν i ε₁ u h := by
  classical
  let q : ℝ := banditOptimalMean ν - ε₂
  let p₀ : ℝ := banditArmMean ν i + ε₁
  let A : ℝ := Real.log (klucbExploration n)
  let D : ℝ := bernoulliRelativeEntropy p₀ q
  have hmi : banditArmMean ν i ∈ Set.Icc (0 : ℝ) 1 := by
    rw [banditArmMean_bernoulli_over μvec hμ ν hν i]
    exact hμ i
  have hma : banditArmMean ν a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [banditArmMean_bernoulli_over μvec hμ ν hν a]
    exact hμ a
  have hp₀q : p₀ < q := by
    dsimp [p₀, q]
    unfold banditGap at hεsum
    linarith
  have hp₀pos : 0 < p₀ := by
    dsimp [p₀]
    linarith [hmi.1]
  have hq : q ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le hp₀pos hp₀q.le
    · dsimp [q]
      rw [← ha]
      linarith [hma.2]
  have hp₀ : p₀ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hp₀pos.le, hp₀q.le.trans hq.2.le⟩
  have hDpos : 0 < D := by
    have hpinsker :=
      bernoulli_relative_entropy_pinsker p₀ q hp₀ hq
    dsimp [D]
    have hne : p₀ - q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hp₀q)
    nlinarith [sq_pos_of_ne_zero hne]
  have hA : 0 ≤ A := by
    dsimp [A]
    apply Real.log_nonneg
    rw [klucbExploration]
    nlinarith [mul_nonneg (Nat.cast_nonneg n)
      (sq_nonneg (Real.log n))]
  let R : Finset (Fin n) :=
    Finset.univ.filter fun r ↦
      (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
        (h r).1 = i ∧
          klucbTruncatedRelativeEntropy
              (armEmpiricalMean i (banditHistoryPrefixAt h r)) q ≤
            Real.log (klucbExploration (r.val + 1)) /
              armPullCount i (banditHistoryPrefixAt h r)
  let f : Fin n → ℕ :=
    fun r ↦ armPullCount i (banditHistoryPrefixAt h r)
  have hR_selected :
      ∀ r ∈ R, (h r).1 = i := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.2.1
  have himage : R.image f ⊆ Finset.Icc 1 n := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨r, hrR, rfl⟩
    have hr := (Finset.mem_filter.mp hrR).2
    exact Finset.mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr (hr.1 i),
        (armPullCount_le_horizon_over i
          (banditHistoryPrefixAt h r)).trans (Nat.le_of_lt r.isLt)⟩
  have hcharge (u : ℕ) (hu : u ∈ R.image f) :
      (if (u : ℝ) ≤ A / D then (1 : ℝ)
        else klOvershootTailIndicatorOver ν i ε₁ u h) = 1 := by
    rcases Finset.mem_image.mp hu with ⟨r, hrR, rfl⟩
    have hr := (Finset.mem_filter.mp hrR).2
    by_cases hsmall :
        (armPullCount i (banditHistoryPrefixAt h r) : ℝ) ≤ A / D
    · rw [if_pos hsmall]
    · rw [if_neg hsmall]
      have hAmono :
          Real.log (klucbExploration (r.val + 1)) ≤ A := by
        dsimp [A]
        exact log_klucbExploration_mono_over
          (by omega) (by omega)
      have hemp :
          p₀ ≤ armEmpiricalMean i (banditHistoryPrefixAt h r) :=
        (feasible_event_implies_small_or_empirical_over
          ν i q p₀ A D hq hp₀ hp₀q rfl hDpos h hh r
          hr.1 hr.2.2 hAmono).resolve_left hsmall
      have hcenter :
          ε₁ ≤ armEmpiricalMean i (banditHistoryPrefixAt h r) -
            banditArmMean ν i := by
        dsimp [p₀] at hemp
        linarith
      have hu_nonneg :
          (0 : ℝ) ≤ armPullCount i (banditHistoryPrefixAt h r) :=
        Nat.cast_nonneg _
      have htail :
          (armPullCount i (banditHistoryPrefixAt h r) : ℝ) * ε₁ ≤
            armStoppedCenteredSum ν i
              (armPullCount i (banditHistoryPrefixAt h r)) n h := by
        rw [armStoppedCenteredSum_stable_after_prefix_over
          ν i h r (armPullCount i (banditHistoryPrefixAt h r)) rfl]
        rw [armStoppedCenteredSum_eq_pullCount_mul_over
          ν i (armPullCount i (banditHistoryPrefixAt h r))
          (banditHistoryPrefixAt h r) le_rfl]
        exact mul_le_mul_of_nonneg_left hcenter hu_nonneg
      unfold klOvershootTailIndicatorOver
      rw [if_pos htail]
  have hcount :
      (klucbFeasibilityFailureCount ν a i ε₂ h).2 =
        (R.card : ℝ) := by
    simp only [klucbFeasibilityFailureCount]
    rw [show R = Finset.univ.filter fun r ↦
      (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
        (h r).1 = i ∧
          klucbTruncatedRelativeEntropy
              (armEmpiricalMean i (banditHistoryPrefixAt h r)) q ≤
            Real.log (klucbExploration (r.val + 1)) /
              armPullCount i (banditHistoryPrefixAt h r) by rfl]
    exact Finset.sum_boole _ _
  rw [hcount]
  have hcardImage :
      (R.image f).card = R.card :=
    Finset.card_image_of_injOn
      (selected_prefix_count_injOn_over i h R hR_selected)
  calc
    (R.card : ℝ) =
        ∑ u ∈ R.image f,
          (if (u : ℝ) ≤ A / D then (1 : ℝ)
            else klOvershootTailIndicatorOver ν i ε₁ u h) := by
      rw [← hcardImage]
      symm
      calc
        (∑ u ∈ R.image f,
            if (u : ℝ) ≤ A / D then (1 : ℝ)
              else klOvershootTailIndicatorOver ν i ε₁ u h) =
            ∑ _u ∈ R.image f, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact hcharge u hu
        _ = ((R.image f).card : ℝ) := by simp
    _ ≤ ∑ u ∈ Finset.Icc 1 n,
          (if (u : ℝ) ≤ A / D then (1 : ℝ)
            else klOvershootTailIndicatorOver ν i ε₁ u h) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro u huI huNot
      split
      · norm_num
      · unfold klOvershootTailIndicatorOver
        split <;> norm_num
    _ ≤ A / D + ∑ u ∈ Finset.Icc 1 n,
          klOvershootTailIndicatorOver ν i ε₁ u h := by
      apply sum_small_or_tail_le_over n (A / D)
      · exact div_nonneg hA hDpos.le
      · intro u
        unfold klOvershootTailIndicatorOver
        split <;> norm_num
    _ = Real.log (klucbExploration n) /
          bernoulliRelativeEntropy
            (banditArmMean ν i + ε₁)
            (banditOptimalMean ν - ε₂) +
        ∑ u ∈ Finset.Icc 1 n,
          klOvershootTailIndicatorOver ν i ε₁ u h := by
      rfl

private theorem measurableSet_initialized_prefix_over
    {k n : ℕ} (r : Fin n) :
    MeasurableSet {h : BanditHistory k n |
      ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0} := by
  classical
  convert MeasurableSet.iInter (fun j : Fin k ↦
    (measurableSet_eq_fun
      ((measurable_armPullCount_over j).comp
        (measurable_banditHistoryPrefixAt_over r))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ (0 : ℝ)))).compl) using 1
  ext h
  simp

private theorem measurable_truncatedEntropy_empirical_over
    {k m : ℕ} (j : Fin k) (q : ℝ) :
    Measurable (fun h : BanditHistory k m ↦
      klucbTruncatedRelativeEntropy (armEmpiricalMean j h) q) := by
  have hemp := measurable_armEmpiricalMean_over (m := m) j
  unfold klucbTruncatedRelativeEntropy bernoulliRelativeEntropy
  apply Measurable.ite (measurableSet_le hemp measurable_const)
  · exact
      (hemp.mul ((hemp.div_const q).log)).add
        ((measurable_const.sub hemp).mul
          (((measurable_const.sub hemp).div_const (1 - q)).log))
  · exact measurable_const

private theorem measurable_feasibilityCount_snd_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).2) := by
  classical
  simp only [klucbFeasibilityFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hsel : MeasurableSet
        {h : BanditHistory k n | (h r).1 = i} :=
      measurableSet_eq_fun
        (measurable_fst.comp (measurable_pi_apply r))
        (measurable_const :
          Measurable (fun _ : BanditHistory k n ↦ i))
    have hbudget : Measurable
        (fun h : BanditHistory k n ↦
          Real.log (klucbExploration (r.val + 1)) /
            armPullCount i (banditHistoryPrefixAt h r)) :=
      measurable_const.div
        ((measurable_armPullCount_over i).comp
          (measurable_banditHistoryPrefixAt_over r))
    have hd : Measurable
        (fun h : BanditHistory k n ↦
          klucbTruncatedRelativeEntropy
            (armEmpiricalMean i (banditHistoryPrefixAt h r))
            (banditOptimalMean ν - ε)) :=
      (measurable_truncatedEntropy_empirical_over i
        (banditOptimalMean ν - ε)).comp
          (measurable_banditHistoryPrefixAt_over r)
    convert ((measurableSet_initialized_prefix_over r).inter hsel).inter
      (measurableSet_le hd hbudget) using 1
    ext h
    simp [and_assoc]
  · exact measurable_const
  · exact measurable_const

private theorem feasibilityCount_snd_nonneg_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (klucbFeasibilityFailureCount ν a i ε h).2 := by
  classical
  simp only [klucbFeasibilityFailureCount]
  positivity

private theorem feasibilityCount_snd_le_horizon_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (klucbFeasibilityFailureCount ν a i ε h).2 ≤ n := by
  classical
  unfold klucbFeasibilityFailureCount
  calc
    (∑ r : Fin n,
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            (h r).1 = i ∧
              klucbTruncatedRelativeEntropy
                  (armEmpiricalMean i (banditHistoryPrefixAt h r))
                  (banditOptimalMean ν - ε) ≤
                Real.log (klucbExploration (r.val + 1)) /
                  armPullCount i (banditHistoryPrefixAt h r)
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem integrable_feasibilityCount_snd_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).2)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_feasibilityCount_snd_over ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨feasibilityCount_snd_nonneg_over ν a i ε h,
        feasibilityCount_snd_le_horizon_over ν a i ε h⟩

private theorem exp_neg_two_mul_sum_Icc_le_over
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∑ u ∈ Finset.Icc 1 n,
        Real.exp (-2 * (u : ℝ) * ε ^ 2) ≤
      1 / (2 * ε ^ 2) := by
  let q : ℝ := Real.exp (-(2 * ε ^ 2))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [sq_pos_of_pos hε]
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_add_one_iff]
  have hsum : ∑ u ∈ Finset.Icc 1 n, q ^ u ≤ q / (1 - q) := by
    rw [le_div_iff₀ hden]
    rw [hIcc, geom_sum_Ico_mul_neg q (by omega : 1 ≤ n + 1)]
    have hpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq0 _
    simp only [pow_one]
    linarith
  have ha : 0 < 2 * ε ^ 2 := by positivity
  have hqa : q / (1 - q) ≤ 1 / (2 * ε ^ 2) := by
    have hqpos : 0 < q := Real.exp_pos _
    have hexp : 1 + 2 * ε ^ 2 ≤ Real.exp (2 * ε ^ 2) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * ε ^ 2)
    have hmain : (2 * ε ^ 2) * q ≤ 1 - q := by
      have := mul_le_mul_of_nonneg_right hexp hqpos.le
      dsimp [q] at this ⊢
      rw [← Real.exp_add] at this
      norm_num at this
      linarith
    rw [div_le_div_iff₀ hden ha]
    nlinarith
  calc
    ∑ u ∈ Finset.Icc 1 n,
        Real.exp (-2 * (u : ℝ) * ε ^ 2) =
        ∑ u ∈ Finset.Icc 1 n, q ^ u := by
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [q]
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ q / (1 - q) := hsum
    _ ≤ 1 / (2 * ε ^ 2) := hqa

end BanditAlgorithm

namespace BanditAlgorithm

private theorem indexCount_eq_feasibilityCount_on_support
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (hq : banditOptimalMean ν - ε ∈ Set.Ioo (0 : ℝ) 1)
    (h : BanditHistory k n) (hh : HistoryRewardsBernoulliOver h) :
    (klucbFailureCount ν a i ε h).2 =
      (klucbFeasibilityFailureCount ν a i ε h).2 := by
  classical
  simp only [klucbFailureCount, klucbFeasibilityFailureCount]
  apply Finset.sum_congr rfl
  intro r hr
  have hthreshold := klucb_index_threshold_feasible i
    (banditHistoryPrefixAt h r) (banditOptimalMean ν - ε) hq
    (empiricalMean_mem_Icc_over i (banditHistoryPrefixAt h r)
      (historyRewardsBernoulliOver_prefix h hh r))
  simp only [hthreshold, and_comm, and_assoc]

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k)
    (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε₁ ε₂ : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hgap : 0 < banditGap ν i)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hεsum : ε₁ + ε₂ < banditGap ν i) :
    integral (banditMeasure ν π n)
        (fun h ↦ (klucbFailureCount ν a i ε₂ h).2) ≤
      Real.log (klucbExploration n) /
          bernoulliRelativeEntropy
            (banditArmMean ν i + ε₁)
            (banditOptimalMean ν - ε₂) +
        1 / (2 * ε₁ ^ 2) := by
  have hmi := hμ i
  have hma := hμ a
  rw [← banditArmMean_bernoulli_over μvec hμ ν hν i] at hmi
  rw [← banditArmMean_bernoulli_over μvec hμ ν hν a, ha] at hma
  have hq : banditOptimalMean ν - ε₂ ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [banditGap] at hεsum
    constructor <;> linarith [hmi.1, hma.2]
  have hsupport := banditMeasure_ae_historyRewardsBernoulliOver μvec hμ ν hν π n
  have heq : (fun h : BanditHistory k n ↦ (klucbFailureCount ν a i ε₂ h).2)
      =ᵐ[banditMeasure ν π n]
        (fun h ↦ (klucbFeasibilityFailureCount ν a i ε₂ h).2) := by
    filter_upwards [hsupport] with h hh
    exact indexCount_eq_feasibilityCount_on_support ν a i ε₂ hq h hh
  have hleft : Integrable
      (fun h : BanditHistory k n ↦ (klucbFailureCount ν a i ε₂ h).2)
      (banditMeasure ν π n) :=
    (integrable_feasibilityCount_snd_over ν π a i ε₂).congr heq.symm
  let B := Real.log (klucbExploration n) /
    bernoulliRelativeEntropy (banditArmMean ν i + ε₁) (banditOptimalMean ν - ε₂)
  have htail (u : ℕ) :=
    integrable_klOvershootTailIndicator_over (n := n) ν π i ε₁ u
  have hsum : Integrable
      (fun h : BanditHistory k n ↦
        ∑ u ∈ Finset.Icc 1 n, klOvershootTailIndicatorOver ν i ε₁ u h)
      (banditMeasure ν π n) :=
    integrable_finsetSum _ (fun u _ ↦ htail u)
  have hsg : IsSubgaussianBandit (1 / 2) ν := by
    rw [hν]
    exact bernoulliBandit_isSubgaussian_half μvec hμ
  calc
    integral (banditMeasure ν π n)
        (fun h ↦ (klucbFailureCount ν a i ε₂ h).2) ≤
      ∫ h, B + ∑ u ∈ Finset.Icc 1 n, klOvershootTailIndicatorOver ν i ε₁ u h
        ∂banditMeasure ν π n := by
      apply integral_mono_ae hleft ((integrable_const B).add hsum)
      filter_upwards [hsupport, heq] with h hh heq'
      rw [heq']
      exact feasibilityCount_snd_le_budget_add_tail_over
        μvec hμ ν hν a i ε₁ ε₂ ha hgap hε₁ hε₂ hεsum h hh
    _ = B + ∑ u ∈ Finset.Icc 1 n,
        ∫ h, klOvershootTailIndicatorOver ν i ε₁ u h ∂banditMeasure ν π n := by
      rw [integral_add (integrable_const B) hsum,
        integral_finsetSum _ (fun u _ ↦ htail u)]
      simp
    _ ≤ B + ∑ u ∈ Finset.Icc 1 n, Real.exp (-2 * (u : ℝ) * ε₁ ^ 2) := by
      apply add_le_add (le_refl B)
      exact Finset.sum_le_sum fun u _ ↦
        integral_klOvershootTailIndicator_le_over ν hsg π i ε₁ u hε₁
    _ ≤ B + 1 / (2 * ε₁ ^ 2) :=
      add_le_add (le_refl B) (exp_neg_two_mul_sum_Icc_le_over n hε₁)

#print axioms solution
