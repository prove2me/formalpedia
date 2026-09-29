-- Prove2me | solution 2 for BanditAlgorithm.klucb_feasibility_optimal_underestimation_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T06:11:34.64868+00:00
-- url     : https://prove2.me/submissions/1ebc4461-4a9e-4996-b6fb-fa7ac2175878

import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail_half
import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_bernoulli_kl_lower_tail
import Theorems.Thm_BanditAlgorithm_bernoulliBandit_isSubgaussian_half
import Theorems.Thm_BanditAlgorithm_bernoulliRelativeEntropy_antitone_fst
import Theorems.Thm_BanditAlgorithm_bernoulli_relative_entropy_pinsker
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_schedule_reciprocal_sum_bound
import Definitions.Def_klucbFeasibilityFailureCount
import Mathlib.Data.Fintype.Order
import Mathlib.Analysis.Complex.ExponentialBounds

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

private theorem bernoulliRelativeEntropy_three_point_lower_low
    {p q μ : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hpq : p ≤ q) (hqμ : q < μ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hμ : μ ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulliRelativeEntropy p q + 2 * (q - μ) ^ 2 ≤
      bernoulliRelativeEntropy p μ := by
  have hratioPos :
      0 < q * (1 - μ) / (μ * (1 - q)) :=
    div_pos (mul_pos hq.1 (sub_pos.mpr hμ.2))
      (mul_pos hμ.1 (sub_pos.mpr hq.2))
  have hratioLt :
      q * (1 - μ) / (μ * (1 - q)) < 1 := by
    rw [div_lt_one (mul_pos hμ.1 (sub_pos.mpr hq.2))]
    nlinarith
  have hlog :
      Real.log (q * (1 - μ) / (μ * (1 - q))) < 0 :=
    Real.log_neg hratioPos hratioLt
  have hcross :
      0 ≤ (p - q) *
        Real.log (q * (1 - μ) / (μ * (1 - q))) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpq) hlog.le
  have hpOne : 1 - p ≠ 0 := by
    have : p < 1 := hpq.trans_lt hq.2
    exact sub_ne_zero.mpr (ne_of_lt this).symm
  have hidentity :
      bernoulliRelativeEntropy p μ =
        bernoulliRelativeEntropy p q +
          bernoulliRelativeEntropy q μ +
          (p - q) *
            Real.log (q * (1 - μ) / (μ * (1 - q))) := by
    rcases eq_or_ne p 0 with rfl | hp0
    · simp only [bernoulliRelativeEntropy, zero_div, Real.log_zero,
        zero_mul, zero_add, one_div, one_mul, sub_zero]
      rw [Real.log_inv, Real.log_inv,
        Real.log_div (ne_of_gt (sub_pos.mpr hq.2))
          (ne_of_gt (sub_pos.mpr hμ.2)),
        Real.log_div (ne_of_gt hq.1) (ne_of_gt hμ.1),
        Real.log_div
          (mul_ne_zero (ne_of_gt hq.1)
            (ne_of_gt (sub_pos.mpr hμ.2)))
          (mul_ne_zero (ne_of_gt hμ.1)
            (ne_of_gt (sub_pos.mpr hq.2))),
        Real.log_mul (ne_of_gt hq.1)
          (ne_of_gt (sub_pos.mpr hμ.2)),
        Real.log_mul (ne_of_gt hμ.1)
          (ne_of_gt (sub_pos.mpr hq.2))]
      ring
    · rw [bernoulliRelativeEntropy, bernoulliRelativeEntropy,
        bernoulliRelativeEntropy,
        Real.log_div hp0 (ne_of_gt hμ.1),
        Real.log_div hp0 (ne_of_gt hq.1),
        Real.log_div hpOne (ne_of_gt (sub_pos.mpr hμ.2)),
        Real.log_div hpOne (ne_of_gt (sub_pos.mpr hq.2)),
        Real.log_div (ne_of_gt hq.1) (ne_of_gt hμ.1),
        Real.log_div (ne_of_gt (sub_pos.mpr hq.2))
          (ne_of_gt (sub_pos.mpr hμ.2)),
        Real.log_div
          (mul_ne_zero (ne_of_gt hq.1)
            (ne_of_gt (sub_pos.mpr hμ.2)))
          (mul_ne_zero (ne_of_gt hμ.1)
            (ne_of_gt (sub_pos.mpr hq.2))),
        Real.log_mul (ne_of_gt hq.1)
          (ne_of_gt (sub_pos.mpr hμ.2)),
        Real.log_mul (ne_of_gt hμ.1)
          (ne_of_gt (sub_pos.mpr hq.2))]
      ring
  have hpinsker :
      2 * (q - μ) ^ 2 ≤ bernoulliRelativeEntropy q μ :=
    bernoulli_relative_entropy_pinsker q μ
      ⟨hq.1.le, hq.2.le⟩ hμ
  rw [hidentity]
  linarith

end BanditAlgorithm
namespace BanditAlgorithm

private theorem banditStepKernel_ae_selected_arm_low
    {k : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    {m : ℕ} (h : BanditHistory k m) (a : Fin k)
    (hselect : (π.select m) h = Measure.dirac a) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.1 = a := by
  let μ := banditStepKernel ν π m h
  have hfst : Measure.map Prod.fst μ = Measure.dirac a := by
    rw [← Kernel.fst_apply, banditStepKernel, Kernel.fst_compProd]
    exact hselect
  have hmap : ∀ᵐ b ∂Measure.map Prod.fst μ, b = a := by
    rw [hfst]
    simp
  exact
    (ae_map_iff (μ := μ) measurable_fst.aemeasurable
      (by measurability)).1 hmap

private theorem banditStepKernel_ae_obeys_initialization_low
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsKLUCBPolicy π) {m : ℕ}
    (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h,
      (∃ j, armPullCount j h = 0) → armPullCount z.1 h = 0 := by
  obtain ⟨a, hdirac, hunpulled, _⟩ := hπ m h
  filter_upwards
    [banditStepKernel_ae_selected_arm_low ν π h a hdirac] with z hz
  simpa [hz] using hunpulled

private def LastStepObeysInitializationLow {k m : ℕ}
    (h : BanditHistory k (m + 1)) : Prop :=
  (∃ j, armPullCount j (Fin.init h) = 0) →
    armPullCount (h (Fin.last m)).1 (Fin.init h) = 0

private def HistoryObeysInitializationLow {k : ℕ} :
    {m : ℕ} → BanditHistory k m → Prop
  | 0, _ => True
  | m + 1, h =>
      HistoryObeysInitializationLow (Fin.init h) ∧
        LastStepObeysInitializationLow h

private theorem measurableSet_initialization_rule_for_arm_low
    {k m : ℕ} (a : Fin k) :
    MeasurableSet {h : BanditHistory k m |
      (∃ j, armPullCount j h = 0) → armPullCount a h = 0} := by
  classical
  have hz (j : Fin k) :
      MeasurableSet {h : BanditHistory k m | armPullCount j h = 0} := by
    simpa only [Nat.cast_eq_zero] using
      measurableSet_eq_fun (measurable_armPullCount_over j)
        (measurable_const :
          Measurable (fun _ : BanditHistory k m ↦ (0 : ℝ)))
  have hExists :
      MeasurableSet {h : BanditHistory k m |
        ∃ j, armPullCount j h = 0} := by
    convert MeasurableSet.iUnion (fun j : Fin k ↦ hz j) using 1
    ext h
    simp
  convert hExists.compl.union (hz a) using 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
  constructor
  · intro himp
    by_cases hex : ∃ j, armPullCount j h = 0
    · exact Or.inr (himp hex)
    · exact Or.inl hex
  · intro hor hex
    rcases hor with hn | ha
    · exact False.elim (hn hex)
    · exact ha

private theorem measurableSet_lastStepObeysInitialization_low
    {k m : ℕ} :
    MeasurableSet {h : BanditHistory k (m + 1) |
      LastStepObeysInitializationLow h} := by
  classical
  have hlast : Measurable
      (fun h : BanditHistory k (m + 1) ↦ (h (Fin.last m)).1) :=
    measurable_fst.comp (measurable_pi_apply (Fin.last m))
  have hinit : Measurable
      (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
    fun_prop
  have hpiece (a : Fin k) : MeasurableSet
      ({h : BanditHistory k (m + 1) | (h (Fin.last m)).1 = a} ∩
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) ⁻¹'
          {q | (∃ j, armPullCount j q = 0) →
            armPullCount a q = 0}) := by
    exact (measurableSet_eq_fun hlast measurable_const).inter
      ((measurableSet_initialization_rule_for_arm_low a).preimage hinit)
  convert MeasurableSet.iUnion (fun a : Fin k ↦ hpiece a) using 1
  ext h
  simp [LastStepObeysInitializationLow]

private theorem measurableSet_historyObeysInitialization_low
    {k : ℕ} : ∀ m : ℕ,
    MeasurableSet {h : BanditHistory k m |
      HistoryObeysInitializationLow h} := by
  intro m
  induction m with
  | zero => simp [HistoryObeysInitializationLow]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        fun_prop
      change MeasurableSet
        ({h : BanditHistory k (m + 1) |
            HistoryObeysInitializationLow (Fin.init h)} ∩
          {h : BanditHistory k (m + 1) |
            LastStepObeysInitializationLow h})
      exact (ih.preimage hinit).inter
        measurableSet_lastStepObeysInitialization_low

private theorem banditMeasure_ae_historyObeysInitialization_low
    {k : ℕ} (ν : StochasticBandit k) {π : BanditPolicy k}
    (hπ : IsKLUCBPolicy π) : ∀ m : ℕ,
    ∀ᵐ h ∂banditMeasure ν π m, HistoryObeysInitializationLow h := by
  intro m
  induction m with
  | zero => simp [banditMeasure, HistoryObeysInitializationLow]
  | succ m ih =>
      have hset := measurableSet_historyObeysInitialization_low
        (k := k) (m + 1)
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih] with h hh
        filter_upwards
          [banditStepKernel_ae_obeys_initialization_low ν hπ h] with z hz
        rw [HistoryObeysInitializationLow,
          LastStepObeysInitializationLow]
        simp only [Fin.init_snoc, Fin.snoc_last]
        exact ⟨hh, hz⟩

private noncomputable def initializationSelectedCountLow
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ r : Fin n,
    if (h r).1 = i ∧
        ¬(∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0)
      then 1 else 0

private theorem initializationSelectedCountLow_snoc
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    initializationSelectedCountLow i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      initializationSelectedCountLow i h +
        if z.1 = i ∧ ¬(∀ j, armPullCount j h ≠ 0)
          then 1 else 0 := by
  classical
  simp only [initializationSelectedCountLow, Fin.sum_univ_castSucc,
    prefixAt_snoc_castSucc_over, prefixAt_snoc_last_over, Fin.snoc_last]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [show
    Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z r.castSucc = h r by
      simp [Fin.snoc, r.isLt]]
  rfl

private theorem initializationSelectedCountLow_le_pullCount
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n) :
    initializationSelectedCountLow i h ≤ armPullCount i h := by
  classical
  rw [initializationSelectedCountLow,
    pullCount_cast_eq_sum_indicator_over]
  apply Finset.sum_le_sum
  intro r hr
  by_cases hi : (h r).1 = i
  · by_cases hex :
        ∃ j, armPullCount j (banditHistoryPrefixAt h r) = 0
    · simp [hi, hex]
    · simp [hi, hex]
  · simp [hi]

private theorem initializationSelectedCountLow_le_one
    {k n : ℕ} (i : Fin k) (h : BanditHistory k n)
    (hh : HistoryObeysInitializationLow h) :
    initializationSelectedCountLow i h ≤ 1 := by
  induction n with
  | zero => simp [initializationSelectedCountLow]
  | succ n ih =>
      rw [← Fin.snoc_init_self h] at hh ⊢
      rw [initializationSelectedCountLow_snoc]
      rcases hh with ⟨hhprev, hhlast⟩
      simp only [Fin.init_snoc] at hhprev
      rw [LastStepObeysInitializationLow] at hhlast
      simp only [Fin.init_snoc, Fin.snoc_last] at hhlast
      by_cases hc :
          (h (Fin.last n)).1 = i ∧
            ¬(∀ j, armPullCount j (Fin.init h) ≠ 0)
      · rw [if_pos hc]
        have hex : ∃ j, armPullCount j (Fin.init h) = 0 := by
          push_neg at hc
          exact hc.2
        have hzero :
            armPullCount i (Fin.init h) = 0 := by
          have := hhlast hex
          simpa [hc.1] using this
        have hinitZero :
            initializationSelectedCountLow i (Fin.init h) = 0 := by
          have hnonneg :
              0 ≤ initializationSelectedCountLow i (Fin.init h) := by
            exact Finset.sum_nonneg fun r hr ↦ by
              split <;> norm_num
          have hle :=
            initializationSelectedCountLow_le_pullCount i (Fin.init h)
          rw [hzero, Nat.cast_zero] at hle
          linarith
        norm_num [hinitZero]
      · rw [if_neg hc]
        simpa using ih (Fin.init h) hhprev

end BanditAlgorithm
namespace BanditAlgorithm

private noncomputable def klUnderTailIndicatorLow
    {k m : ℕ} (μvec : Fin k → ℝ) (ν : StochasticBandit k)
    (a : Fin k) (ε : ℝ) (u : ℕ) (h : BanditHistory k m) : ℝ :=
  let stoppedAverage :=
    (armStoppedCenteredSum ν a u m h + μvec a * (u : ℝ)) / (u : ℝ)
  let c :=
    Real.log (klucbExploration (m + 1)) / (u : ℝ) + 2 * ε ^ 2
  if u ≤ armPullCount a h ∧
      stoppedAverage ∈ Set.Icc (0 : ℝ) 1 ∧
      stoppedAverage < μvec a ∧
      c < bernoulliRelativeEntropy stoppedAverage (μvec a)
    then 1 else 0

private theorem measurable_klUnderTailIndicator_low
    {k m : ℕ} (μvec : Fin k → ℝ) (ν : StochasticBandit k)
    (a : Fin k) (ε : ℝ) (u : ℕ) :
    Measurable (klUnderTailIndicatorLow μvec ν a ε u :
      BanditHistory k m → ℝ) := by
  let avg : BanditHistory k m → ℝ := fun h ↦
    (armStoppedCenteredSum ν a u m h + μvec a * (u : ℝ)) / (u : ℝ)
  have havg : Measurable avg :=
    ((measurable_armStoppedCenteredSum_over ν a u m).add_const _).div_const _
  have hcount : Measurable
      (fun h : BanditHistory k m ↦ (armPullCount a h : ℝ)) :=
    measurable_armPullCount_over a
  have hcountSet :
      MeasurableSet {h : BanditHistory k m | u ≤ armPullCount a h} := by
    have hs : MeasurableSet {h : BanditHistory k m |
        (u : ℝ) ≤ (armPullCount a h : ℝ)} :=
      measurableSet_le measurable_const hcount
    simpa only [Nat.cast_le] using hs
  have havgIcc : MeasurableSet {h : BanditHistory k m |
      avg h ∈ Set.Icc (0 : ℝ) 1} :=
    (measurableSet_le measurable_const havg).inter
      (measurableSet_le havg measurable_const)
  have havgLt : MeasurableSet {h : BanditHistory k m |
      avg h < μvec a} :=
    measurableSet_lt havg measurable_const
  have hentropy : Measurable (fun h : BanditHistory k m ↦
      bernoulliRelativeEntropy (avg h) (μvec a)) := by
    unfold bernoulliRelativeEntropy
    exact
      (havg.mul ((havg.div_const (μvec a)).log)).add
        ((measurable_const.sub havg).mul
          (((measurable_const.sub havg).div_const
            (1 - μvec a)).log))
  unfold klUnderTailIndicatorLow
  apply Measurable.ite
  · convert (((hcountSet.inter havgIcc).inter havgLt).inter
      (measurableSet_lt
        (measurable_const : Measurable (fun _ : BanditHistory k m ↦
          Real.log (klucbExploration (m + 1)) / (u : ℝ) +
            2 * ε ^ 2))
        hentropy)) using 1
    ext h
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    simp [avg, and_assoc]
  · exact measurable_const
  · exact measurable_const

private theorem integrable_klUnderTailIndicator_low
    {k m : ℕ} (μvec : Fin k → ℝ) (ν : StochasticBandit k)
    (π : BanditPolicy k) (a : Fin k) (ε : ℝ) (u : ℕ) :
    Integrable (klUnderTailIndicatorLow μvec ν a ε u)
      (banditMeasure ν π m) := by
  apply Integrable.of_bound
    (measurable_klUnderTailIndicator_low
      (m := m) μvec ν a ε u).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun h ↦ by
    dsimp [klUnderTailIndicatorLow]
    split <;> norm_num

private theorem integral_klUnderTailIndicator_eq_probability_low
    {k m : ℕ} (μvec : Fin k → ℝ) (ν : StochasticBandit k)
    (π : BanditPolicy k) (a : Fin k) (ε : ℝ) (u : ℕ) :
    (∫ h, klUnderTailIndicatorLow μvec ν a ε u h
        ∂banditMeasure ν π m) =
      (banditMeasure ν π m).real
        {h : BanditHistory k m |
          let stoppedAverage :=
            (armStoppedCenteredSum ν a u m h + μvec a * (u : ℝ)) /
              (u : ℝ)
          let c :=
            Real.log (klucbExploration (m + 1)) / (u : ℝ) +
              2 * ε ^ 2
          u ≤ armPullCount a h ∧
            stoppedAverage ∈ Set.Icc (0 : ℝ) 1 ∧
            stoppedAverage < μvec a ∧
            c < bernoulliRelativeEntropy stoppedAverage (μvec a)} := by
  let E : Set (BanditHistory k m) :=
    {h |
      let stoppedAverage :=
        (armStoppedCenteredSum ν a u m h + μvec a * (u : ℝ)) /
          (u : ℝ)
      let c :=
        Real.log (klucbExploration (m + 1)) / (u : ℝ) + 2 * ε ^ 2
      u ≤ armPullCount a h ∧
        stoppedAverage ∈ Set.Icc (0 : ℝ) 1 ∧
        stoppedAverage < μvec a ∧
        c < bernoulliRelativeEntropy stoppedAverage (μvec a)}
  have hE : MeasurableSet E := by
    have hm := measurable_klUnderTailIndicator_low
      (m := m) μvec ν a ε u
    have heq : E =
        {h : BanditHistory k m |
          klUnderTailIndicatorLow μvec ν a ε u h = 1} := by
      ext h
      dsimp [E, klUnderTailIndicatorLow]
      split <;> simp_all
    rw [heq]
    exact measurableSet_eq_fun hm measurable_const
  have hfun :
      (klUnderTailIndicatorLow μvec ν a ε u :
        BanditHistory k m → ℝ) =
        E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext h
    unfold klUnderTailIndicatorLow
    change (if h ∈ E then (1 : ℝ) else 0) =
      E.indicator (fun _ ↦ (1 : ℝ)) h
    by_cases hh : h ∈ E <;> simp [Set.indicator, hh]
  rw [hfun]
  exact integral_indicator_one hE

private theorem integral_klUnderTailIndicator_le_low
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (a : Fin k) (ε : ℝ) (u : ℕ)
    (hu : 0 < u) (hμa0 : 0 < μvec a) (hμa1 : μvec a < 1) :
    (∫ h, klUnderTailIndicatorLow μvec ν a ε u h
        ∂banditMeasure ν π m) ≤
      Real.exp (-((u : ℝ) *
        (Real.log (klucbExploration (m + 1)) / (u : ℝ) +
          2 * ε ^ 2))) := by
  rw [integral_klUnderTailIndicator_eq_probability_low]
  exact bandit_adaptive_stopped_bernoulli_kl_lower_tail
    (n := m) μvec hμ ν hν (π := π) a u hu hμa0 hμa1
    (Real.log (klucbExploration (m + 1)) / (u : ℝ) +
      2 * ε ^ 2)

private noncomputable def optimalBadIndicatorLow
    {k m : ℕ} (ν : StochasticBandit k) (a : Fin k)
    (ε : ℝ) (h : BanditHistory k m) : ℝ :=
  if (∀ j, armPullCount j h ≠ 0) ∧
      Real.log (klucbExploration (m + 1)) / armPullCount a h <
        klucbTruncatedRelativeEntropy (armEmpiricalMean a h)
          (banditOptimalMean ν - ε)
    then 1 else 0

private theorem optimalBadIndicatorLow_le_tails
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (a : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) (hqpos : 0 < μvec a - ε)
    (hμa1 : μvec a < 1)
    (h : BanditHistory k m) (hh : HistoryRewardsBernoulliOver h) :
    optimalBadIndicatorLow ν a ε h ≤
      ∑ u ∈ Finset.Icc 1 m,
        klUnderTailIndicatorLow μvec ν a ε u h := by
  classical
  unfold optimalBadIndicatorLow
  split
  next hbad =>
    let u := armPullCount a h
    have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (hbad.1 a)
    have hum : u ≤ m := armPullCount_le_horizon_over a h
    have huMem : u ∈ Finset.Icc 1 m := by simp [hu1, hum]
    have hμa : banditArmMean ν a = μvec a :=
      banditArmMean_bernoulli_over μvec hμ ν hν a
    have hμa0 : 0 < μvec a := by linarith
    let q := μvec a - ε
    have hq : q ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · simpa [q] using hqpos
      · dsimp [q]
        linarith
    have hμaIoo : μvec a ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hμa0, hμa1⟩
    have hemp :
        armEmpiricalMean a h ∈ Set.Icc (0 : ℝ) 1 :=
      empiricalMean_mem_Icc_over a h hh
    have hlognonneg :
        0 ≤ Real.log (klucbExploration (m + 1)) :=
      Real.log_nonneg (by
        rw [klucbExploration]
        exact le_add_of_nonneg_right
          (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    have hcountpos : (0 : ℝ) < armPullCount a h := by
      exact_mod_cast hu1
    have hbudgetNonneg :
        0 ≤ Real.log (klucbExploration (m + 1)) /
          armPullCount a h :=
      div_nonneg hlognonneg hcountpos.le
    have hempq : armEmpiricalMean a h ≤ q := by
      by_contra hn
      have hgt : q < armEmpiricalMean a h := lt_of_not_ge hn
      have hz :
          klucbTruncatedRelativeEntropy (armEmpiricalMean a h) q = 0 := by
        rw [klucbTruncatedRelativeEntropy,
          if_neg (not_le_of_gt hgt)]
      rw [← ha, hμa] at hbad
      have hbad2 := hbad.2
      change _ <
        klucbTruncatedRelativeEntropy (armEmpiricalMean a h) q at hbad2
      rw [hz] at hbad2
      linarith
    have hbridge :
        bernoulliRelativeEntropy (armEmpiricalMean a h) q +
            2 * ε ^ 2 ≤
          bernoulliRelativeEntropy (armEmpiricalMean a h) (μvec a) := by
      have hthree :=
        bernoulliRelativeEntropy_three_point_lower_low
          hemp hempq (by dsimp [q]; linarith) hq hμaIoo
      convert hthree using 1 <;> dsimp [q] <;> ring
    have hbad' :
        Real.log (klucbExploration (m + 1)) / (u : ℝ) +
            2 * ε ^ 2 <
          bernoulliRelativeEntropy (armEmpiricalMean a h) (μvec a) := by
      rw [← ha, hμa] at hbad
      have hbad2 := hbad.2
      change
        Real.log (klucbExploration (m + 1)) / (u : ℝ) <
          klucbTruncatedRelativeEntropy (armEmpiricalMean a h) q at hbad2
      rw [klucbTruncatedRelativeEntropy, if_pos hempq] at hbad2
      linarith
    have hstop :
        (armStoppedCenteredSum ν a u m h + μvec a * (u : ℝ)) /
            (u : ℝ) =
          armEmpiricalMean a h := by
      rw [armStoppedCenteredSum_eq_pullCount_mul_over
        ν a u h (by rfl), hμa]
      field_simp
      ring
    calc
      (1 : ℝ) ≤ klUnderTailIndicatorLow μvec ν a ε u h := by
        unfold klUnderTailIndicatorLow
        rw [hstop]
        have huu : u ≤ armPullCount a h := by rfl
        have hempmu : armEmpiricalMean a h < μvec a :=
          hempq.trans_lt (by dsimp [q]; linarith)
        rw [if_pos ⟨huu, hemp, hempmu, hbad'⟩]
      _ ≤ ∑ u ∈ Finset.Icc 1 m,
          klUnderTailIndicatorLow μvec ν a ε u h :=
        Finset.single_le_sum (s := Finset.Icc 1 m)
          (f := fun v ↦ klUnderTailIndicatorLow μvec ν a ε v h)
          (fun v hv ↦ by
            dsimp [klUnderTailIndicatorLow]
            split <;> norm_num)
          huMem
  next hnot =>
    exact Finset.sum_nonneg fun u hu ↦ by
      dsimp [klUnderTailIndicatorLow]
      split <;> norm_num

private theorem measurableSet_initialized_low {k m : ℕ} :
    MeasurableSet {h : BanditHistory k m |
      ∀ j, armPullCount j h ≠ 0} := by
  classical
  convert MeasurableSet.iInter (fun j : Fin k ↦
    (measurableSet_eq_fun (measurable_armPullCount_over j)
      (measurable_const :
        Measurable (fun _ : BanditHistory k m ↦ (0 : ℝ)))).compl) using 1
  ext h
  simp

private theorem measurable_optimalBadIndicator_low
    {k m : ℕ} (ν : StochasticBandit k) (a : Fin k) (ε : ℝ) :
    Measurable (optimalBadIndicatorLow ν a ε :
      BanditHistory k m → ℝ) := by
  have hbudget : Measurable (fun h : BanditHistory k m ↦
      Real.log (klucbExploration (m + 1)) / armPullCount a h) :=
    measurable_const.div (measurable_armPullCount_over a)
  have hd : Measurable (fun h : BanditHistory k m ↦
      klucbTruncatedRelativeEntropy (armEmpiricalMean a h)
        (banditOptimalMean ν - ε)) :=
    measurable_truncatedEntropy_empirical_over a
      (banditOptimalMean ν - ε)
  unfold optimalBadIndicatorLow
  exact Measurable.ite
    (measurableSet_initialized_low.inter
      (measurableSet_lt hbudget hd))
    measurable_const measurable_const

private theorem integrable_optimalBadIndicator_low
    {k m : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a : Fin k) (ε : ℝ) :
    Integrable (optimalBadIndicatorLow ν a ε)
      (banditMeasure ν π m) := by
  apply Integrable.of_bound
    (measurable_optimalBadIndicator_low ν a ε).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun h ↦ by
    unfold optimalBadIndicatorLow
    split <;> norm_num

private theorem exp_kl_tail_sum_le_low
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∑ u ∈ Finset.Icc 1 m,
        Real.exp (-((u : ℝ) *
          (Real.log (klucbExploration (m + 1)) / (u : ℝ) +
            2 * ε ^ 2))) ≤
      1 / klucbExploration (m + 1) * (1 / (2 * ε ^ 2)) := by
  have hfpos : 0 < klucbExploration (m + 1) :=
    klucbExploration_pos_over (m + 1)
  calc
    ∑ u ∈ Finset.Icc 1 m,
        Real.exp (-((u : ℝ) *
          (Real.log (klucbExploration (m + 1)) / (u : ℝ) +
            2 * ε ^ 2))) =
      1 / klucbExploration (m + 1) *
        ∑ u ∈ Finset.Icc 1 m,
          Real.exp (-2 * (u : ℝ) * ε ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
      have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hu1)
      rw [show 1 / klucbExploration (m + 1) =
          Real.exp (-Real.log (klucbExploration (m + 1))) by
        rw [Real.exp_neg, Real.exp_log hfpos]
        simp [one_div]]
      rw [← Real.exp_add]
      congr 1
      field_simp [hu0]
      ring
    _ ≤ 1 / klucbExploration (m + 1) * (1 / (2 * ε ^ 2)) := by
      apply mul_le_mul_of_nonneg_left
        (exp_neg_two_mul_sum_Icc_le_over m hε)
      exact (one_div_nonneg.mpr hfpos.le)

private theorem integral_optimalBadIndicator_le_low
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (a : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) (hqpos : 0 < μvec a - ε)
    (hμa1 : μvec a < 1) :
    (∫ h, optimalBadIndicatorLow ν a ε h
        ∂banditMeasure ν π m) ≤
      1 / klucbExploration (m + 1) * (1 / (2 * ε ^ 2)) := by
  have hleft :=
    integrable_optimalBadIndicator_low
      (m := m) ν π a ε
  have htails (u : ℕ) :
      Integrable (klUnderTailIndicatorLow
        (m := m) μvec ν a ε u) (banditMeasure ν π m) :=
    integrable_klUnderTailIndicator_low μvec ν π a ε u
  have hμa0 : 0 < μvec a := by linarith
  calc
    (∫ h, optimalBadIndicatorLow ν a ε h
        ∂banditMeasure ν π m) ≤
      ∫ h, ∑ u ∈ Finset.Icc 1 m,
          klUnderTailIndicatorLow μvec ν a ε u h
        ∂banditMeasure ν π m := by
      apply integral_mono_ae hleft
        (integrable_finset_sum (Finset.Icc 1 m)
          fun u hu ↦ htails u)
      filter_upwards
        [banditMeasure_ae_historyRewardsBernoulliOver
          μvec hμ ν hν π m] with h hh
      exact optimalBadIndicatorLow_le_tails
        μvec hμ ν hν a ε ha hε hqpos hμa1 h hh
    _ = ∑ u ∈ Finset.Icc 1 m,
        ∫ h, klUnderTailIndicatorLow μvec ν a ε u h
          ∂banditMeasure ν π m := by
      rw [integral_finset_sum]
      intro u hu
      exact htails u
    _ ≤ ∑ u ∈ Finset.Icc 1 m,
        Real.exp (-((u : ℝ) *
          (Real.log (klucbExploration (m + 1)) / (u : ℝ) +
            2 * ε ^ 2))) := by
      gcongr with u hu
      exact integral_klUnderTailIndicator_le_low
        μvec hμ ν hν π a ε u
          (Finset.mem_Icc.mp hu).1 hμa0 hμa1
    _ ≤ 1 / klucbExploration (m + 1) * (1 / (2 * ε ^ 2)) :=
      exp_kl_tail_sum_le_low m hε

private theorem banditMeasure_map_init_low {k m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) :
    (banditMeasure ν π (m + 1)).map
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) =
      banditMeasure ν π m := by
  rw [banditMeasure]
  rw [Measure.map_map
    (by fun_prop :
      Measurable (fun h : BanditHistory k (m + 1) ↦ Fin.init h))
    measurable_banditHistorySnoc]
  have hfun :
      ((fun h : BanditHistory k (m + 1) ↦ Fin.init h) ∘
        (fun h : BanditHistory k m × (Fin k × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) h.1 h.2)) =
        Prod.fst := by
    funext p
    simp
  rw [hfun]
  change Measure.fst
      ((banditMeasure ν π m).compProd (banditStepKernel ν π m)) =
    banditMeasure ν π m
  exact Measure.fst_compProd
    (banditMeasure ν π m) (banditStepKernel ν π m)

private theorem banditMeasure_map_historyPrefixAt_low
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) :
    (banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) =
      banditMeasure ν π r.val := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h (Fin.last n)) =
            banditMeasure ν π n
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h (Fin.last n)) =
          (fun h ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa using prefixAt_snoc_last_over
              (Fin.init h) (h (Fin.last n))]
        exact banditMeasure_map_init_low ν π
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h s.castSucc) =
            banditMeasure ν π s.val
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h s.castSucc) =
          (fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
            (fun h : BanditHistory k (n + 1) ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa [Function.comp_apply] using
              prefixAt_snoc_castSucc_over
                (Fin.init h) (h (Fin.last n)) s]
        calc
          (banditMeasure ν π (n + 1)).map
              ((fun g : BanditHistory k n ↦
                  banditHistoryPrefixAt g s) ∘
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)) =
              ((banditMeasure ν π (n + 1)).map
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)).map
                (fun g : BanditHistory k n ↦
                  banditHistoryPrefixAt g s) := by
            symm
            exact Measure.map_map
              (measurable_banditHistoryPrefixAt_over s)
              (by fun_prop :
                Measurable
                  (fun h : BanditHistory k (n + 1) ↦ Fin.init h))
          _ = banditMeasure ν π s.val := by
            rw [banditMeasure_map_init_low ν π, ih s]

private noncomputable def optimalBadCountLow
    {k n : ℕ} (ν : StochasticBandit k) (a : Fin k)
    (ε : ℝ) (h : BanditHistory k n) : ℝ :=
  ∑ r : Fin n,
    optimalBadIndicatorLow ν a ε (banditHistoryPrefixAt h r)

private theorem feasibilityCount_fst_le_init_add_bad_low
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k)
    (ε : ℝ) (h : BanditHistory k n) :
    (klucbFeasibilityFailureCount ν a i ε h).1 ≤
      initializationSelectedCountLow i h +
        optimalBadCountLow ν a ε h := by
  classical
  unfold klucbFeasibilityFailureCount
  change (∑ r : Fin n,
      if (h r).1 = i ∧
          (¬(∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∨
            Real.log (klucbExploration (r.val + 1)) /
                armPullCount a (banditHistoryPrefixAt h r) <
              klucbTruncatedRelativeEntropy
                (armEmpiricalMean a (banditHistoryPrefixAt h r))
                (banditOptimalMean ν - ε))
        then (1 : ℝ) else 0) ≤
    initializationSelectedCountLow i h +
      optimalBadCountLow ν a ε h
  rw [initializationSelectedCountLow, optimalBadCountLow,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  unfold optimalBadIndicatorLow
  by_cases hi : (h r).1 = i
  · by_cases hinit :
        ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0
    · by_cases hbad :
        Real.log (klucbExploration (r.val + 1)) /
              armPullCount a (banditHistoryPrefixAt h r) <
            klucbTruncatedRelativeEntropy
              (armEmpiricalMean a (banditHistoryPrefixAt h r))
              (banditOptimalMean ν - ε)
      · simp [hi, hinit, hbad]
      · simp [hi, hinit, hbad]
    · simp [hi, hinit]
  · simp only [hi, false_and, if_false, zero_add]
    split <;> norm_num

private theorem measurable_optimalBadCount_low
    {k n : ℕ} (ν : StochasticBandit k) (a : Fin k) (ε : ℝ) :
    Measurable (optimalBadCountLow ν a ε :
      BanditHistory k n → ℝ) := by
  unfold optimalBadCountLow
  apply Finset.measurable_sum
  intro r hr
  exact (measurable_optimalBadIndicator_low
    (m := r.val) ν a ε).comp
      (measurable_banditHistoryPrefixAt_over r)

private theorem integrable_optimalBadCount_low
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a : Fin k) (ε : ℝ) :
    Integrable (optimalBadCountLow ν a ε)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_optimalBadCount_low ν a ε).aemeasurable
  · filter_upwards [] with h
    constructor
    · unfold optimalBadCountLow
      exact Finset.sum_nonneg fun r hr ↦ by
        unfold optimalBadIndicatorLow
        split <;> norm_num
    · unfold optimalBadCountLow
      calc
        (∑ r : Fin n,
            optimalBadIndicatorLow ν a ε
              (banditHistoryPrefixAt h r)) ≤
            ∑ _r : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          unfold optimalBadIndicatorLow
          split <;> norm_num
        _ = n := by simp

private theorem optimalBadIndicatorLow_eq_zero_of_lt_two
    {k m : ℕ} (ν : StochasticBandit k) (a i : Fin k)
    (hai : a ≠ i) (ε : ℝ) (hm : m < 2)
    (h : BanditHistory k m) :
    optimalBadIndicatorLow ν a ε h = 0 := by
  interval_cases m
  · unfold optimalBadIndicatorLow
    rw [if_neg]
    intro hbad
    exact hbad.1 a (by simp [armPullCount])
  · unfold optimalBadIndicatorLow
    rw [if_neg]
    intro hbad
    have ha0 := hbad.1 a
    have hi0 := hbad.1 i
    simp only [armPullCount] at ha0 hi0
    have haeq : (h 0).1 = a := by
      by_contra hne
      simp [hne] at ha0
    have hieq : (h 0).1 = i := by
      by_contra hne
      simp [hne] at hi0
    exact hai (haeq.symm.trans hieq)

private theorem sum_fin_succ_if_two_eq_Icc_low
    (n : ℕ) (f : ℕ → ℝ) :
    ∑ r : Fin n, (if (2 : ℕ) ≤ r.val then f (r.val + 1) else (0 : ℝ)) =
      ∑ t ∈ Finset.Icc 3 n, f t := by
  change (∑ r : Fin n,
      (fun j : ℕ ↦ if 2 ≤ j then f (j + 1) else (0 : ℝ)) r.val) =
    ∑ t ∈ Finset.Icc 3 n, f t
  calc
    (∑ r : Fin n,
      (fun j : ℕ ↦ if 2 ≤ j then f (j + 1) else (0 : ℝ)) r.val) =
        ∑ j ∈ Finset.range n, if 2 ≤ j then f (j + 1) else 0 :=
      Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ if 2 ≤ j then f (j + 1) else (0 : ℝ)) n
    _ =
        ∑ j ∈ (Finset.range n).filter (fun j ↦ 2 ≤ j),
          f (j + 1) := by
      rw [Finset.sum_filter]
    _ = ∑ t ∈ Finset.Icc 3 n, f t := by
      apply Finset.sum_bij (fun j _ ↦ j + 1)
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        simp [hj.2, hj.1]
      · intro j₁ hj₁ j₂ hj₂ heq
        omega
      · intro t ht
        have ht' := Finset.mem_Icc.mp ht
        refine ⟨t - 1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          omega
        · omega
      · intro j hj
        rfl

private theorem klucb_schedule_tail_three_le_one_low (n : ℕ) :
    ∑ t ∈ Finset.Icc 3 n, 1 / klucbExploration t ≤ 1 := by
  by_cases hn : n < 3
  · have hempty : Finset.Icc 3 n = ∅ := by
      ext t
      simp
      omega
    rw [hempty]
    simp
  have hn3 : 3 ≤ n := Nat.le_of_not_gt hn
  have hsame (t : ℕ) :
      asymptoticUcbSchedule t = klucbExploration t := by
    rfl
  have htotal :
      ∑ t ∈ Finset.Icc 1 n, 1 / klucbExploration t ≤ 5 / 2 := by
    simpa only [hsame] using
      asymptotic_ucb_schedule_reciprocal_sum_bound n
  have hf1 : klucbExploration 1 = 1 := by
    simp [klucbExploration]
  have hlog0 : 0 ≤ Real.log (2 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlog1 : Real.log (2 : ℝ) < 1 := by
    linarith [Real.log_two_lt_d9]
  have hlogle : Real.log (2 : ℝ) ≤ 7 / 10 := by
    linarith [Real.log_two_lt_d9]
  have hprod :
      0 ≤ (7 / 10 - Real.log (2 : ℝ)) *
        (7 / 10 + Real.log (2 : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hlogle)
      (by linarith)
  have hf2le : klucbExploration 2 ≤ 2 := by
    rw [klucbExploration]
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hf2pos : 0 < klucbExploration 2 :=
    klucbExploration_pos_over 2
  have hhalf : (1 / 2 : ℝ) ≤ 1 / klucbExploration 2 :=
    one_div_le_one_div_of_le hf2pos hf2le
  have hdecomp :
      ∑ t ∈ Finset.Icc 1 n, 1 / klucbExploration t =
        1 / klucbExploration 1 + 1 / klucbExploration 2 +
          ∑ t ∈ Finset.Icc 3 n, 1 / klucbExploration t := by
    have hset :
        Finset.Icc 1 n =
          {1, 2} ∪ Finset.Icc 3 n := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hset, Finset.sum_union]
    · simp
    · simp
  rw [hdecomp, hf1] at htotal
  norm_num at hhalf htotal ⊢
  linarith

private theorem integral_optimalBadCount_le_low
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (a i : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hai : a ≠ i) (hε : 0 < ε) (hqpos : 0 < μvec a - ε)
    (hμa1 : μvec a < 1) :
    (∫ h, optimalBadCountLow ν a ε h
        ∂banditMeasure ν π n) ≤
      1 / (2 * ε ^ 2) := by
  have hterm (r : Fin n) :
      (∫ h, optimalBadIndicatorLow ν a ε
          (banditHistoryPrefixAt h r)
          ∂banditMeasure ν π n) ≤
        if 2 ≤ r.val then
          1 / klucbExploration (r.val + 1) *
            (1 / (2 * ε ^ 2))
        else 0 := by
    by_cases hr2 : 2 ≤ r.val
    · rw [if_pos hr2]
      calc
        (∫ h, optimalBadIndicatorLow ν a ε
            (banditHistoryPrefixAt h r)
            ∂banditMeasure ν π n) =
          ∫ q, optimalBadIndicatorLow ν a ε q
            ∂(banditMeasure ν π n).map
              (fun h : BanditHistory k n ↦
                banditHistoryPrefixAt h r) := by
            rw [integral_map
              (measurable_banditHistoryPrefixAt_over r).aemeasurable
              (measurable_optimalBadIndicator_low
                (m := r.val) ν a ε).aestronglyMeasurable]
        _ = ∫ q, optimalBadIndicatorLow ν a ε q
            ∂banditMeasure ν π r.val := by
          rw [banditMeasure_map_historyPrefixAt_low]
        _ ≤ 1 / klucbExploration (r.val + 1) *
              (1 / (2 * ε ^ 2)) :=
          integral_optimalBadIndicator_le_low
            μvec hμ ν hν π a ε ha hε hqpos hμa1
    · rw [if_neg hr2]
      have hrlt : r.val < 2 := Nat.lt_of_not_ge hr2
      have hzero :
          (fun h : BanditHistory k n ↦
            optimalBadIndicatorLow ν a ε
              (banditHistoryPrefixAt h r)) = fun _ ↦ 0 := by
        funext h
        exact optimalBadIndicatorLow_eq_zero_of_lt_two
          ν a i hai ε hrlt (banditHistoryPrefixAt h r)
      rw [hzero]
      simp
  have hcountInt :=
    integrable_optimalBadCount_low
      (n := n) ν π a ε
  calc
    (∫ h, optimalBadCountLow ν a ε h
        ∂banditMeasure ν π n) =
      ∑ r : Fin n,
        ∫ h, optimalBadIndicatorLow ν a ε
          (banditHistoryPrefixAt h r)
          ∂banditMeasure ν π n := by
      unfold optimalBadCountLow
      rw [integral_finset_sum]
      intro r hr
      apply Integrable.of_bound
        ((measurable_optimalBadIndicator_low
          (m := r.val) ν a ε).comp
            (measurable_banditHistoryPrefixAt_over r)).aestronglyMeasurable 1
      filter_upwards [] with h
      dsimp [Function.comp_apply, optimalBadIndicatorLow]
      split <;> norm_num
    _ ≤ ∑ r : Fin n,
        if 2 ≤ r.val then
          1 / klucbExploration (r.val + 1) *
            (1 / (2 * ε ^ 2))
        else 0 := by
      gcongr with r
      exact hterm r
    _ = (∑ t ∈ Finset.Icc 3 n,
          1 / klucbExploration t) * (1 / (2 * ε ^ 2)) := by
      rw [show
        (∑ r : Fin n,
          if 2 ≤ r.val then
            1 / klucbExploration (r.val + 1) *
              (1 / (2 * ε ^ 2))
          else 0) =
        ∑ t ∈ Finset.Icc 3 n,
          (1 / klucbExploration t) * (1 / (2 * ε ^ 2)) by
            exact sum_fin_succ_if_two_eq_Icc_low n
              (fun t ↦
                (1 / klucbExploration t) * (1 / (2 * ε ^ 2)))]
      rw [Finset.sum_mul]
    _ ≤ 1 * (1 / (2 * ε ^ 2)) := by
      apply mul_le_mul_of_nonneg_right
        (klucb_schedule_tail_three_le_one_low n)
      positivity
    _ = 1 / (2 * ε ^ 2) := by ring

private def HistoryArmOneLow {k n : ℕ}
    (a : Fin k) (h : BanditHistory k n) : Prop :=
  ∀ t, (h t).1 = a → (h t).2 = 1

private theorem measurableSet_historyArmOne_low
    {k n : ℕ} (a : Fin k) :
    MeasurableSet {h : BanditHistory k n | HistoryArmOneLow a h} := by
  classical
  convert MeasurableSet.iInter (fun t : Fin n ↦
    (measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply t))
      (measurable_const :
        Measurable (fun _ : BanditHistory k n ↦ a))).compl.union
      (measurableSet_eq_fun
        (measurable_snd.comp (measurable_pi_apply t))
        (measurable_const :
          Measurable (fun _ : BanditHistory k n ↦ (1 : ℝ))))) using 1
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union,
    Set.mem_compl_iff]
  constructor
  · intro hall t
    by_cases ht : (h t).1 = a
    · exact Or.inr (hall t ht)
    · exact Or.inl ht
  · intro hor t ht
    rcases hor t with hne | hone
    · exact False.elim (hne ht)
    · exact hone

private theorem bernoulli_arm_mean_one_ae_low
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (a : Fin k) (hμa : μvec a = 1) :
    ∀ᵐ x ∂ν.P a, x = 1 := by
  rw [hν, bernoulliBandit]
  simp [hμa]

private theorem banditStepKernel_ae_armOne_low
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (a : Fin k) (hμa : μvec a = 1)
    (h : BanditHistory k m) :
    ∀ᵐ z ∂banditStepKernel ν π m h, z.1 = a → z.2 = 1 := by
  rw [banditStepKernel]
  apply Kernel.ae_compProd_of_ae_ae
  · convert
      (measurableSet_eq_fun
        (measurable_fst :
          Measurable (fun z : Fin k × ℝ ↦ z.1))
        (measurable_const :
          Measurable (fun _ : Fin k × ℝ ↦ a))).compl.union
        (measurableSet_eq_fun
          (measurable_snd :
            Measurable (fun z : Fin k × ℝ ↦ z.2))
          (measurable_const :
            Measurable (fun _ : Fin k × ℝ ↦ (1 : ℝ)))) using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
    constructor
    · intro himp
      by_cases hza : z.1 = a
      · exact Or.inr (himp hza)
      · exact Or.inl hza
    · intro hor hza
      rcases hor with hne | hone
      · exact False.elim (hne hza)
      · exact hone
  · filter_upwards with j
    rw [Kernel.comap_apply]
    by_cases hja : j = a
    · subst j
      filter_upwards
        [bernoulli_arm_mean_one_ae_low μvec hμ ν hν a hμa] with x hx
      intro _
      exact hx
    · exact Filter.Eventually.of_forall fun x hsel ↦
        False.elim (hja hsel)

private theorem banditMeasure_ae_historyArmOne_low
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (a : Fin k) (hμa : μvec a = 1) :
    ∀ n : ℕ, ∀ᵐ h ∂banditMeasure ν π n, HistoryArmOneLow a h := by
  intro n
  induction n with
  | zero => simp [banditMeasure, HistoryArmOneLow]
  | succ n ih =>
      have hset := measurableSet_historyArmOne_low
        (n := n + 1) a
      rw [banditMeasure]
      rw [ae_map_iff measurable_banditHistorySnoc.aemeasurable hset]
      apply Measure.ae_compProd_of_ae_ae
      · exact measurable_banditHistorySnoc hset
      · filter_upwards [ih] with h hh
        filter_upwards
          [banditStepKernel_ae_armOne_low
            μvec hμ ν hν π a hμa h] with z hz
        intro t
        refine Fin.lastCases ?_ (fun s ↦ ?_) t
        · simp only [Fin.snoc_last]
          exact hz
        · simp only [Fin.snoc_castSucc]
          exact hh s

private theorem empiricalMean_eq_one_of_historyArmOne_low
    {k n : ℕ} (a : Fin k) (h : BanditHistory k n)
    (hh : HistoryArmOneLow a h) (hcount : armPullCount a h ≠ 0) :
    armEmpiricalMean a h = 1 := by
  let S : Finset (Fin n) := {t | (h t).1 = a}.toFinset
  have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = a) := by
    ext t
    simp [S]
  have hnum :
      (∑ t ∈ {t | (h t).1 = a}.toFinset, (h t).2) =
        S.card := by
    change (∑ t ∈ S, (h t).2) = S.card
    calc
      (∑ t ∈ S, (h t).2) = ∑ _t ∈ S, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        apply hh t
        rw [hS] at ht
        exact (Finset.mem_filter.mp ht).2
      _ = S.card := by simp
  have hcard : S.card = armPullCount a h := by
    rw [armPullCount]
  unfold armEmpiricalMean
  rw [hnum, hcard]
  exact div_self (by exact_mod_cast hcount)

private theorem optimalBadIndicatorLow_eq_zero_mean_one
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (a : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) (hμa : μvec a = 1)
    (h : BanditHistory k m) (hh : HistoryArmOneLow a h) :
    optimalBadIndicatorLow ν a ε h = 0 := by
  unfold optimalBadIndicatorLow
  rw [if_neg]
  intro hbad
  have hemp : armEmpiricalMean a h = 1 :=
    empiricalMean_eq_one_of_historyArmOne_low a h hh (hbad.1 a)
  have hmean : banditArmMean ν a = 1 := by
    rw [banditArmMean_bernoulli_over μvec hμ ν hν a, hμa]
  have hq : banditOptimalMean ν - ε < 1 := by
    rw [← ha, hmean]
    linarith
  have hd :
      klucbTruncatedRelativeEntropy (armEmpiricalMean a h)
          (banditOptimalMean ν - ε) = 0 := by
    rw [klucbTruncatedRelativeEntropy,
      if_neg (by rw [hemp]; exact not_le_of_gt hq)]
  have hlognonneg :
      0 ≤ Real.log (klucbExploration (m + 1)) :=
    Real.log_nonneg (by
      rw [klucbExploration]
      exact le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  have hcountpos : (0 : ℝ) < armPullCount a h := by
    exact_mod_cast Nat.pos_of_ne_zero (hbad.1 a)
  rw [hd] at hbad
  have := div_nonneg hlognonneg hcountpos.le
  linarith

private theorem integral_optimalBadCount_mean_one_eq_zero
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (a : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hε : 0 < ε) (hμa : μvec a = 1) :
    (∫ h, optimalBadCountLow ν a ε h
        ∂banditMeasure ν π n) = 0 := by
  have hzero :
      ∀ᵐ h ∂banditMeasure ν π n,
        optimalBadCountLow ν a ε h = 0 := by
    filter_upwards
      [banditMeasure_ae_historyArmOne_low
        μvec hμ ν hν π a hμa n] with h hh
    unfold optimalBadCountLow
    apply Finset.sum_eq_zero
    intro r hr
    exact optimalBadIndicatorLow_eq_zero_mean_one
      μvec hμ ν hν a ε ha hε hμa
        (banditHistoryPrefixAt h r)
        (fun t ht ↦ hh
          (⟨t.val, lt_trans t.isLt r.isLt⟩ : Fin n) ht)
  simpa using integral_congr_ae hzero

private theorem measurable_initializationSelectedCountLow
    {k n : ℕ} (i : Fin k) :
    Measurable (initializationSelectedCountLow i :
      BanditHistory k n → ℝ) := by
  unfold initializationSelectedCountLow
  apply Finset.measurable_sum
  intro r hr
  have hsel : MeasurableSet {h : BanditHistory k n | (h r).1 = i} :=
    measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply r))
      measurable_const
  exact Measurable.ite
    (hsel.inter (measurableSet_initialized_prefix_over r).compl)
    measurable_const measurable_const

private theorem integrable_initializationSelectedCountLow
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) :
    Integrable (initializationSelectedCountLow i)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_initializationSelectedCountLow i).aemeasurable
  · filter_upwards [] with h
    constructor
    · unfold initializationSelectedCountLow
      exact Finset.sum_nonneg fun r hr ↦ by split <;> norm_num
    · unfold initializationSelectedCountLow
      calc
        (∑ r : Fin n,
          if (h r).1 = i ∧
              ¬(∀ j,
                armPullCount j (banditHistoryPrefixAt h r) ≠ 0)
            then (1 : ℝ) else 0) ≤
            ∑ _r : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          split <;> norm_num
        _ = n := by simp

private theorem measurable_feasibilityCount_fst_low
    {k n : ℕ} (ν : StochasticBandit k)
    (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).1) := by
  simp only [klucbFeasibilityFailureCount]
  apply Finset.measurable_sum
  intro r hr
  have hsel : MeasurableSet {h : BanditHistory k n | (h r).1 = i} :=
    measurableSet_eq_fun
      (measurable_fst.comp (measurable_pi_apply r))
      measurable_const
  have hbudget : Measurable (fun h : BanditHistory k n ↦
      Real.log (klucbExploration (r.val + 1)) /
        armPullCount a (banditHistoryPrefixAt h r)) :=
    measurable_const.div
      ((measurable_armPullCount_over a).comp
        (measurable_banditHistoryPrefixAt_over r))
  have hd : Measurable (fun h : BanditHistory k n ↦
      klucbTruncatedRelativeEntropy
        (armEmpiricalMean a (banditHistoryPrefixAt h r))
        (banditOptimalMean ν - ε)) :=
    (measurable_truncatedEntropy_empirical_over a
      (banditOptimalMean ν - ε)).comp
        (measurable_banditHistoryPrefixAt_over r)
  exact Measurable.ite
    (hsel.inter
      ((measurableSet_initialized_prefix_over r).compl.union
        (measurableSet_lt hbudget hd)))
    measurable_const measurable_const

private theorem integrable_feasibilityCount_fst_low
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (klucbFeasibilityFailureCount ν a i ε h).1)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact
      (measurable_feasibilityCount_fst_low ν a i ε).aemeasurable
  · filter_upwards [] with h
    constructor
    · simp only [klucbFeasibilityFailureCount]
      exact Finset.sum_nonneg fun r hr ↦ by split <;> norm_num
    · simp only [klucbFeasibilityFailureCount]
      calc
        (∑ r : Fin n,
          if (h r).1 = i ∧
              (¬(∀ j,
                armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∨
                Real.log (klucbExploration (r.val + 1)) /
                    armPullCount a (banditHistoryPrefixAt h r) <
                  klucbTruncatedRelativeEntropy
                    (armEmpiricalMean a (banditHistoryPrefixAt h r))
                    (banditOptimalMean ν - ε))
            then (1 : ℝ) else 0) ≤
            ∑ _r : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro r hr
          split <;> norm_num
        _ = n := by simp

private theorem integral_initializationSelectedCountLow_le_one
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (hπ : IsKLUCBPolicy π) (i : Fin k) :
    (∫ h, initializationSelectedCountLow i h
        ∂banditMeasure ν π n) ≤ 1 := by
  have hint :=
    integrable_initializationSelectedCountLow
      (n := n) ν π i
  calc
    (∫ h, initializationSelectedCountLow i h
        ∂banditMeasure ν π n) ≤
      ∫ _h, (1 : ℝ) ∂banditMeasure ν π n := by
        apply integral_mono_ae hint (integrable_const 1)
        filter_upwards
          [banditMeasure_ae_historyObeysInitialization_low
            ν hπ n] with h hh
        exact initializationSelectedCountLow_le_one i h hh
    _ = 1 := by simp

end BanditAlgorithm

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsKLUCBPolicy π)
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hε : 0 < ε)
    (hεgap : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1) ≤
      2 / ε ^ 2 := by
  have hμa :
      BanditAlgorithm.banditArmMean ν a = μvec a :=
    BanditAlgorithm.banditArmMean_bernoulli_over
      μvec hμ ν hν a
  have hμi :
      BanditAlgorithm.banditArmMean ν i = μvec i :=
    BanditAlgorithm.banditArmMean_bernoulli_over
      μvec hμ ν hν i
  have hai : a ≠ i := by
    intro hai
    subst i
    rw [BanditAlgorithm.banditGap, ← ha] at hεgap
    linarith
  have hqpos : 0 < μvec a - ε := by
    rw [← hμa, ha]
    rw [BanditAlgorithm.banditGap] at hεgap
    have hmi0 : 0 ≤ BanditAlgorithm.banditArmMean ν i := by
      rw [hμi]
      exact (hμ i).1
    linarith
  have hgaple : BanditAlgorithm.banditGap ν i ≤ 1 := by
    rw [BanditAlgorithm.banditGap]
    have hop1 : BanditAlgorithm.banditOptimalMean ν ≤ 1 := by
      rw [← ha, hμa]
      exact (hμ a).2
    have hmi0 : 0 ≤ BanditAlgorithm.banditArmMean ν i := by
      rw [hμi]
      exact (hμ i).1
    linarith
  have hε1 : ε < 1 := hεgap.trans_le hgaple
  have hbad :
      (∫ h, BanditAlgorithm.optimalBadCountLow ν a ε h
          ∂BanditAlgorithm.banditMeasure ν π n) ≤
        1 / (2 * ε ^ 2) := by
    by_cases hμa1eq : μvec a = 1
    · rw [BanditAlgorithm.integral_optimalBadCount_mean_one_eq_zero
        μvec hμ ν hν π a ε ha hε hμa1eq]
      positivity
    · have hμa1 : μvec a < 1 :=
        lt_of_le_of_ne (hμ a).2 hμa1eq
      exact BanditAlgorithm.integral_optimalBadCount_le_low
        μvec hμ ν hν π a i ε ha hai hε hqpos hμa1
  have hleft :=
    BanditAlgorithm.integrable_feasibilityCount_fst_low
      (n := n) ν π a i ε
  have hinit :=
    BanditAlgorithm.integrable_initializationSelectedCountLow
      (n := n) ν π i
  have hbadInt :=
    BanditAlgorithm.integrable_optimalBadCount_low
      (n := n) ν π a ε
  calc
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1) ≤
      ∫ h, BanditAlgorithm.initializationSelectedCountLow i h +
          BanditAlgorithm.optimalBadCountLow ν a ε h
        ∂BanditAlgorithm.banditMeasure ν π n := by
      apply integral_mono_ae hleft (hinit.add hbadInt)
      filter_upwards [] with h
      exact
        BanditAlgorithm.feasibilityCount_fst_le_init_add_bad_low
          ν a i ε h
    _ = (∫ h, BanditAlgorithm.initializationSelectedCountLow i h
          ∂BanditAlgorithm.banditMeasure ν π n) +
        ∫ h, BanditAlgorithm.optimalBadCountLow ν a ε h
          ∂BanditAlgorithm.banditMeasure ν π n := by
      rw [integral_add hinit hbadInt]
    _ ≤ 1 + 1 / (2 * ε ^ 2) := by
      gcongr
      exact
        BanditAlgorithm.integral_initializationSelectedCountLow_le_one
          ν π hπ i
    _ ≤ 2 / ε ^ 2 := by
      have hεsq : ε ^ 2 ≤ 1 := by nlinarith
      have hεsqpos : 0 < ε ^ 2 := sq_pos_of_pos hε
      have hone : 1 ≤ (ε ^ 2)⁻¹ :=
        (one_le_inv₀ hεsqpos).2 hεsq
      have hsecond :
          1 / (2 * ε ^ 2) ≤ (ε ^ 2)⁻¹ := by
        rw [div_le_iff₀ (by positivity : 0 < 2 * ε ^ 2)]
        field_simp [ne_of_gt hεsqpos]
        norm_num
      calc
        1 + 1 / (2 * ε ^ 2) ≤
            (ε ^ 2)⁻¹ + (ε ^ 2)⁻¹ :=
          add_le_add hone hsecond
        _ = 2 / ε ^ 2 := by
          field_simp [ne_of_gt hεsqpos]
          norm_num
