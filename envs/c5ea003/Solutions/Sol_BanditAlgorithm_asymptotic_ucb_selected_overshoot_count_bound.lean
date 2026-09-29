-- Prove2me | solution 1 for BanditAlgorithm.asymptotic_ucb_selected_overshoot_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-28T16:25:06.759919+00:00
-- url     : https://prove2.me/submissions/7d2e1b6f-a81b-4aef-8c79-4320482b0f1b

import Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_centered_sum_tail
import Theorems.Thm_BanditAlgorithm_bandit_ucb_index_exponential_sum_bound_sharp
import Definitions.Def_asymptoticUcbFailureCount
import Mathlib.Data.Fintype.Order

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

private theorem measurable_asymptoticUcbIndex_over
    {k m : ℕ} (i : Fin k) :
    Measurable (asymptoticUcbIndex (n := m) i) := by
  unfold asymptoticUcbIndex
  apply (measurable_armEmpiricalMean_over i).add
  exact Measurable.sqrt
    (measurable_const.div (measurable_armPullCount_over i))

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

private theorem asymptoticUcbSchedule_pos_over (t : ℕ) :
    0 < asymptoticUcbSchedule t := by
  simp only [asymptoticUcbSchedule]
  positivity

private theorem asymptoticUcbSchedule_mono_over
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    asymptoticUcbSchedule s ≤ asymptoticUcbSchedule t := by
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
  simpa only [asymptoticUcbSchedule, add_comm] using add_le_add_left hprod 1

private theorem log_asymptoticUcbSchedule_mono_over
    {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Real.log (asymptoticUcbSchedule s) ≤
      Real.log (asymptoticUcbSchedule t) :=
  Real.strictMonoOn_log.monotoneOn
    (asymptoticUcbSchedule_pos_over s)
    (asymptoticUcbSchedule_pos_over t)
    (asymptoticUcbSchedule_mono_over hs hst)

private theorem sqrt_ucb_bonus_mono_over
    {s t u : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Real.sqrt
        (2 * Real.log (asymptoticUcbSchedule s) / (u : ℝ)) ≤
      Real.sqrt
        (2 * Real.log (asymptoticUcbSchedule t) / (u : ℝ)) := by
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (log_asymptoticUcbSchedule_mono_over hs hst) (by norm_num))
    (Nat.cast_nonneg _)

private noncomputable def overshootTailSetOver
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) : Set (BanditHistory k n) :=
  if 2 * Real.log (asymptoticUcbSchedule n) /
      (banditGap ν i - ε) ^ 2 < (u : ℝ) then
    {h |
      (u : ℝ) *
          (banditGap ν i - ε -
            Real.sqrt
              (2 * Real.log (asymptoticUcbSchedule n) / (u : ℝ))) ≤
        armStoppedCenteredSum ν i u n h}
  else Set.univ

private noncomputable def overshootTailIndicatorOver
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) (h : BanditHistory k n) : ℝ := by
  classical
  exact if h ∈ overshootTailSetOver ν i ε u then 1 else 0

private theorem failureCount_snd_le_tail_sum_over
    {k n : ℕ} (ν : StochasticBandit k)
    (a i : Fin k) (ε : ℝ) (h : BanditHistory k n) :
    (asymptoticUcbFailureCount ν a i ε h).2 ≤
      ∑ u ∈ Finset.Icc 1 n,
        overshootTailIndicatorOver ν i ε u h := by
  classical
  let R : Finset (Fin n) :=
    Finset.univ.filter fun r ↦
      (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
        banditOptimalMean ν - ε ≤
          asymptoticUcbIndex i (banditHistoryPrefixAt h r) ∧
        (h r).1 = i
  let f : Fin n → ℕ :=
    fun r ↦ armPullCount i (banditHistoryPrefixAt h r)
  have hR_selected :
      ∀ r ∈ R, (h r).1 = i := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.2.2
  have himage :
      R.image f ⊆
        (Finset.Icc 1 n).filter
          (fun u ↦ h ∈ overshootTailSetOver ν i ε u) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨r, hrR, rfl⟩
    have hr := (Finset.mem_filter.mp hrR).2
    have hcount0 :
        armPullCount i (banditHistoryPrefixAt h r) ≠ 0 :=
      hr.1 i
    have hu1 :
        1 ≤ armPullCount i (banditHistoryPrefixAt h r) :=
      Nat.one_le_iff_ne_zero.mpr hcount0
    have hun :
        armPullCount i (banditHistoryPrefixAt h r) ≤ n :=
      (armPullCount_le_horizon_over i
        (banditHistoryPrefixAt h r)).trans
          (Nat.le_of_lt r.isLt)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hu1, hun⟩, ?_⟩
    unfold overshootTailSetOver
    split_ifs with hcut
    · change
        (armPullCount i (banditHistoryPrefixAt h r) : ℝ) *
            (banditGap ν i - ε -
              Real.sqrt
                (2 * Real.log (asymptoticUcbSchedule n) /
                  (armPullCount i
                    (banditHistoryPrefixAt h r) : ℝ))) ≤
          armStoppedCenteredSum ν i
            (armPullCount i (banditHistoryPrefixAt h r)) n h
      have hrschedule :
          Real.sqrt
              (2 * Real.log (asymptoticUcbSchedule (r.val + 1)) /
                (armPullCount i (banditHistoryPrefixAt h r) : ℝ)) ≤
            Real.sqrt
              (2 * Real.log (asymptoticUcbSchedule n) /
                (armPullCount i (banditHistoryPrefixAt h r) : ℝ)) :=
        sqrt_ucb_bonus_mono_over
          (Nat.one_le_iff_ne_zero.mpr (by omega))
          (by omega)
      have hcenter :
          banditGap ν i - ε -
              Real.sqrt
                (2 * Real.log (asymptoticUcbSchedule n) /
                  (armPullCount i (banditHistoryPrefixAt h r) : ℝ)) ≤
            armEmpiricalMean i (banditHistoryPrefixAt h r) -
              banditArmMean ν i := by
        simp only [asymptoticUcbIndex] at hr
        unfold banditGap
        nlinarith [hr.2.1, hrschedule]
      have hmul :=
        mul_le_mul_of_nonneg_left hcenter
          (Nat.cast_nonneg
            (armPullCount i (banditHistoryPrefixAt h r)) : (0 : ℝ) ≤ _)
      rw [armStoppedCenteredSum_stable_after_prefix_over
        ν i h r (armPullCount i (banditHistoryPrefixAt h r)) rfl]
      rw [armStoppedCenteredSum_eq_pullCount_mul_over
        ν i (armPullCount i (banditHistoryPrefixAt h r))
        (banditHistoryPrefixAt h r) le_rfl]
      exact hmul
    · simp
  have hcard :
      R.card ≤
        ((Finset.Icc 1 n).filter
          (fun u ↦ h ∈ overshootTailSetOver ν i ε u)).card := by
    rw [← Finset.card_image_of_injOn
      (selected_prefix_count_injOn_over i h R hR_selected)]
    exact Finset.card_le_card himage
  calc
    (asymptoticUcbFailureCount ν a i ε h).2 =
        (R.card : ℝ) := by
      simp only [asymptoticUcbFailureCount]
      rw [show R = Finset.univ.filter fun r ↦
          (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            banditOptimalMean ν - ε ≤
              asymptoticUcbIndex i (banditHistoryPrefixAt h r) ∧
            (h r).1 = i by rfl]
      exact Finset.sum_boole _ _
    _ ≤
        (((Finset.Icc 1 n).filter
          (fun u ↦ h ∈ overshootTailSetOver ν i ε u)).card : ℝ) := by
      exact_mod_cast hcard
    _ = ∑ u ∈ Finset.Icc 1 n,
        overshootTailIndicatorOver ν i ε u h := by
      unfold overshootTailIndicatorOver
      rw [← Finset.sum_boole]

private theorem measurableSet_overshootTailSet_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) :
    MeasurableSet (overshootTailSetOver (n := n) ν i ε u) := by
  unfold overshootTailSetOver
  split_ifs
  · exact measurableSet_le measurable_const
      (measurable_armStoppedCenteredSum_over ν i u n)
  · exact MeasurableSet.univ

private theorem measurable_overshootTailIndicator_over
    {k n : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (ε : ℝ) (u : ℕ) :
    Measurable (overshootTailIndicatorOver ν i ε u :
      BanditHistory k n → ℝ) := by
  classical
  unfold overshootTailIndicatorOver
  exact Measurable.ite
    (measurableSet_overshootTailSet_over ν i ε u)
    measurable_const measurable_const

private theorem integrable_overshootTailIndicator_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ) :
    Integrable (overshootTailIndicatorOver ν i ε u)
      (banditMeasure ν π n) := by
  apply Integrable.of_bound
    (measurable_overshootTailIndicator_over ν i ε u).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun h ↦ by
    classical
    unfold overshootTailIndicatorOver
    split <;> norm_num

private theorem integral_overshootTailIndicator_eq_probability_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ) :
    (∫ h, overshootTailIndicatorOver ν i ε u h
        ∂banditMeasure ν π n) =
      (banditMeasure ν π n).real
        (overshootTailSetOver (n := n) ν i ε u) := by
  classical
  let E : Set (BanditHistory k n) :=
    overshootTailSetOver (n := n) ν i ε u
  have hE : MeasurableSet E :=
    measurableSet_overshootTailSet_over ν i ε u
  have hfun :
      (overshootTailIndicatorOver ν i ε u :
        BanditHistory k n → ℝ) =
        E.indicator (fun _ ↦ (1 : ℝ)) := by
    funext h
    unfold overshootTailIndicatorOver
    change (if h ∈ E then (1 : ℝ) else 0) =
      E.indicator (fun _ ↦ (1 : ℝ)) h
    by_cases hh : h ∈ E <;> simp [Set.indicator, hh]
  rw [hfun]
  exact integral_indicator_one hE

private theorem sqrt_threshold_lt_over
    {t d A : ℝ} (hd : 0 < d) (hA : 0 < A)
    (ht : 2 * A / d ^ 2 < t) :
    Real.sqrt (2 * A / t) < d := by
  rw [Real.sqrt_lt' hd]
  have ht0 : 0 < t := by
    have hcut : 0 < 2 * A / d ^ 2 := by positivity
    linarith
  rw [div_lt_iff₀ ht0]
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  rw [div_lt_iff₀ hd2] at ht
  nlinarith

private theorem integral_overshootTailIndicator_le_summand_over
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit 1 ν) (π : BanditPolicy k)
    (i : Fin k) (ε : ℝ) (u : ℕ)
    (hd : 0 < banditGap ν i - ε)
    (hA : 0 < Real.log (asymptoticUcbSchedule n))
    (hu : 1 ≤ u) :
    (∫ h, overshootTailIndicatorOver ν i ε u h
        ∂banditMeasure ν π n) ≤
      if 2 * Real.log (asymptoticUcbSchedule n) /
          (banditGap ν i - ε) ^ 2 < (u : ℝ) then
        Real.exp
          (-((u : ℝ) *
              (banditGap ν i - ε -
                Real.sqrt
                  (2 * Real.log (asymptoticUcbSchedule n) /
                    (u : ℝ)))) ^ 2 /
            ((2 : ℝ) * (u : ℝ) * (1 : ℝ)))
      else 1 := by
  rw [integral_overshootTailIndicator_eq_probability_over ν π i ε u]
  split_ifs with hcut
  · rw [overshootTailSetOver, if_pos hcut]
    have ht :
        0 ≤ banditGap ν i - ε -
          Real.sqrt
            (2 * Real.log (asymptoticUcbSchedule n) / (u : ℝ)) :=
      sub_nonneg.mpr
        (sqrt_threshold_lt_over hd hA hcut).le
    have htail :=
      (bandit_adaptive_stopped_centered_sum_tail
        (n := n) (π := π) ν hν i u ht).1
    have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
    have hexponent :
        -(u : ℝ) *
              (banditGap ν i - ε -
                Real.sqrt
                  (2 * Real.log (asymptoticUcbSchedule n) /
                    (u : ℝ))) ^ 2 / 2 =
          -((u : ℝ) *
              (banditGap ν i - ε -
                Real.sqrt
                  (2 * Real.log (asymptoticUcbSchedule n) /
                    (u : ℝ)))) ^ 2 /
            ((2 : ℝ) * (u : ℝ) * (1 : ℝ)) := by
      field_simp [ne_of_gt huR]
    simpa only [hexponent] using htail
  · simp [overshootTailSetOver, hcut]

private theorem measurableSet_initialized_over
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

private theorem measurable_failureCount_snd_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ) :
    Measurable (fun h : BanditHistory k n ↦
      (asymptoticUcbFailureCount ν a i ε h).2) := by
  classical
  simp only [asymptoticUcbFailureCount]
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have hm := ((measurableSet_initialized_over r).inter
        (measurableSet_le
          (measurable_const :
            Measurable (fun _ : BanditHistory k n ↦
              banditOptimalMean ν - ε))
          ((measurable_asymptoticUcbIndex_over i).comp
            (measurable_banditHistoryPrefixAt_over r)))).inter
        (measurableSet_eq_fun
          (measurable_fst.comp (measurable_pi_apply r))
          (measurable_const :
            Measurable (fun _ : BanditHistory k n ↦ i)))
    convert hm using 1
    ext h
    simp [and_assoc]
  · exact measurable_const
  · exact measurable_const

private theorem failureCount_snd_nonneg_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    0 ≤ (asymptoticUcbFailureCount ν a i ε h).2 := by
  classical
  simp only [asymptoticUcbFailureCount]
  positivity

private theorem failureCount_snd_le_horizon_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) :
    (asymptoticUcbFailureCount ν a i ε h).2 ≤ n := by
  classical
  unfold asymptoticUcbFailureCount
  calc
    (∑ r : Fin n,
        if (∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0) ∧
            banditOptimalMean ν - ε ≤
              asymptoticUcbIndex i (banditHistoryPrefixAt h r) ∧
            (h r).1 = i
          then (1 : ℝ) else 0) ≤
        ∑ _r : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      split <;> norm_num
    _ = n := by simp

private theorem integrable_failureCount_snd_over
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (a i : Fin k) (ε : ℝ) :
    Integrable (fun h : BanditHistory k n ↦
      (asymptoticUcbFailureCount ν a i ε h).2)
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_failureCount_snd_over ν a i ε).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦
      ⟨failureCount_snd_nonneg_over ν a i ε h,
        failureCount_snd_le_horizon_over ν a i ε h⟩

private theorem failureCount_snd_eq_zero_of_le_one_over
    {k n : ℕ} (ν : StochasticBandit k) (a i : Fin k)
    (ε : ℝ) (h : BanditHistory k n) (hn : n ≤ 1) :
    (asymptoticUcbFailureCount ν a i ε h).2 = 0 := by
  classical
  simp only [asymptoticUcbFailureCount]
  apply Finset.sum_eq_zero
  intro r hr
  rw [if_neg]
  intro hevent
  have hrzero : r.val = 0 := by omega
  have ha0 := hevent.1 a
  simp [armPullCount] at ha0
  rcases ha0 with ⟨t, ht⟩
  exact Fin.elim0 (Fin.cast hrzero t)

theorem asymptotic_ucb_selected_overshoot_count_bound_proof
    {k : ℕ} {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : banditArmMean ν a = banditOptimalMean ν)
    (hgap : 0 < banditGap ν i)
    (hεpos : 0 < ε)
    (hεlt : ε < banditGap ν i) :
    integral (banditMeasure ν π n)
        (fun h ↦ (asymptoticUcbFailureCount ν a i ε h).2) ≤
      2 / (banditGap ν i - ε) ^ 2 *
        (Real.log (asymptoticUcbSchedule n) +
          Real.sqrt
            (Real.pi * Real.log (asymptoticUcbSchedule n)) +
          1) := by
  classical
  have hd : 0 < banditGap ν i - ε := sub_pos.mpr hεlt
  by_cases hn : n ≤ 1
  · have hfun :
        (fun h : BanditHistory k n ↦
          (asymptoticUcbFailureCount ν a i ε h).2) =
          fun _ ↦ (0 : ℝ) := by
      funext h
      exact failureCount_snd_eq_zero_of_le_one_over
        ν a i ε h hn
    rw [hfun]
    simp only [integral_zero]
    have hn_cases : n = 0 ∨ n = 1 := by omega
    rcases hn_cases with rfl | rfl <;>
      simp [asymptoticUcbSchedule] <;> positivity
  · have hn2 : 2 ≤ n := by omega
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn2
    have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnR
    have hschedule :
        1 < asymptoticUcbSchedule n := by
      simp only [asymptoticUcbSchedule]
      have hnpos : (0 : ℝ) < n := by positivity
      have hlogsq : 0 < Real.log (n : ℝ) ^ 2 :=
        sq_pos_of_pos hlogn
      nlinarith [mul_pos hnpos hlogsq]
    have hA :
        0 < Real.log (asymptoticUcbSchedule n) :=
      Real.log_pos hschedule
    have hright_integrable :
        Integrable
          (fun h : BanditHistory k n ↦
            ∑ u ∈ Finset.Icc 1 n,
              overshootTailIndicatorOver ν i ε u h)
          (banditMeasure ν π n) := by
      exact integrable_finset_sum (Finset.Icc 1 n) fun u hu ↦
        integrable_overshootTailIndicator_over ν π i ε u
    calc
      integral (banditMeasure ν π n)
          (fun h ↦ (asymptoticUcbFailureCount ν a i ε h).2) ≤
          ∫ h,
            (∑ u ∈ Finset.Icc 1 n,
              overshootTailIndicatorOver ν i ε u h)
            ∂banditMeasure ν π n := by
        exact integral_mono
          (integrable_failureCount_snd_over ν π a i ε)
          hright_integrable
          (failureCount_snd_le_tail_sum_over ν a i ε)
      _ =
          ∑ u ∈ Finset.Icc 1 n,
            ∫ h, overshootTailIndicatorOver ν i ε u h
              ∂banditMeasure ν π n := by
        rw [integral_finset_sum]
        intro u hu
        exact integrable_overshootTailIndicator_over ν π i ε u
      _ ≤
          ∑ u ∈ Finset.Icc 1 n,
            if 2 * Real.log (asymptoticUcbSchedule n) /
                (banditGap ν i - ε) ^ 2 < (u : ℝ) then
              Real.exp
                (-((u : ℝ) *
                    (banditGap ν i - ε -
                      Real.sqrt
                        (2 * Real.log (asymptoticUcbSchedule n) /
                          (u : ℝ)))) ^ 2 /
                  ((2 : ℝ) * (u : ℝ) * (1 : ℝ)))
            else 1 := by
        apply Finset.sum_le_sum
        intro u hu
        exact integral_overshootTailIndicator_le_summand_over
          ν hν π i ε u hd hA (Finset.mem_Icc.mp hu).1
      _ ≤
          2 / (banditGap ν i - ε) ^ 2 *
            (Real.log (asymptoticUcbSchedule n) +
              Real.sqrt
                (Real.pi * Real.log (asymptoticUcbSchedule n)) +
              1) :=
        bandit_ucb_index_exponential_sum_bound_sharp hd hA

end BanditAlgorithm

theorem solution
    {k : ℕ} {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hgap : 0 < BanditAlgorithm.banditGap ν i)
    (hεpos : 0 < ε)
    (hεlt : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.asymptoticUcbFailureCount ν a i ε h).2) ≤
      2 / (BanditAlgorithm.banditGap ν i - ε) ^ 2 *
        (Real.log (BanditAlgorithm.asymptoticUcbSchedule n) +
          Real.sqrt
            (Real.pi * Real.log (BanditAlgorithm.asymptoticUcbSchedule n)) +
          1) :=
  BanditAlgorithm.asymptotic_ucb_selected_overshoot_count_bound_proof
    hν n a i ε ha hgap hεpos hεlt
