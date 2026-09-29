-- Prove2me | solution 1 for BanditAlgorithm.mdp_value_diff_le_travel_time
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:50:03.642107+00:00
-- url     : https://prove2.me/submissions/79d31c93-ae87-482f-a834-d5f0837d53a9

import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ
import Theorems.Thm_BanditAlgorithm_mdp_measure_map_restrict

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

/-!
The Bellman inequality, applied along a trajectory stopped when the target
state is first reached, bounds the difference of values by the gain times the
expected travel time (L&S Exercise 38.13).
-/

variable {S A : ℕ}

/-- Restricting a trajectory of `n` rounds to its first `m` rounds. -/
def mdpRestrict {m n : ℕ} (hmn : m ≤ n) (h : MDPTrajectory S A n) :
    MDPTrajectory S A m :=
  fun t ↦ h (Fin.castLE hmn t)

lemma measurable_mdpRestrict {m n : ℕ} (hmn : m ≤ n) :
    Measurable (mdpRestrict (S := S) (A := A) hmn) := by
  rw [measurable_pi_iff]
  exact fun t ↦ measurable_pi_apply _

/-- The integral of a function against the measure of a probability vector on
the states is the corresponding finite sum. -/
lemma integral_mdpStateDistribution (d : MDPStateDistribution S) (f : Fin S → ℝ) :
    ∫ s, f s ∂d.toMeasure = ∑ s, (d.prob s : ℝ) * f s := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have : d.toMeasure {s} = (d.prob s : ℝ≥0∞) := by
    simp only [MDPStateDistribution.toMeasure, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton s), Set.indicator_apply,
      Set.mem_singleton_iff]
    rw [Finset.sum_eq_single s] <;> simp +contextual
  rw [measureReal_def, this, smul_eq_mul]
  simp


/-- The step kernel integrates by first drawing the state, then the action. -/
lemma mdp_integral_stepKernel (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) (h : MDPTrajectory S A n)
    (G : Fin S × Fin A → ℝ) :
    ∫ p, G p ∂(mdpStepKernel M μ0 π n h)
      = ∫ s, (∫ a, G (s, a) ∂(π.select n (h, s))) ∂(mdpStateKernel M μ0 n h) :=
  ProbabilityTheory.integral_compProd Integrable.of_finite


/-- The expected value of the state of the next round, given the trajectory so
far: `⟨P_{A_t}(S_t), v⟩` (and `⟨μ0, v⟩` at the start of the interaction). -/
noncomputable def mdpNextValue (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (v : Fin S → ℝ) (n : ℕ) (h : MDPTrajectory S A n) : ℝ :=
  ∫ s, v s ∂(mdpStateKernel M μ0 n h)

lemma mdpNextValue_succ (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (v : Fin S → ℝ) (n : ℕ) (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    mdpNextValue M μ0 v (n + 1) (Fin.snoc h p) = ∑ s', (M.P p.1 p.2 s' : ℝ) * v s' := by
  rw [mdpNextValue, mdpStateKernel, Kernel.comap_apply]
  simp only [Fin.snoc_last]
  show ∫ s, v s ∂((M.transitionDist p.1 p.2).toMeasure) = _
  rw [integral_mdpStateDistribution]
  rfl

lemma mdpTrajectoryReward_snoc (M : FiniteMDP S A) {n : ℕ}
    (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + M.r p.1 p.2 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  simp

/-- The expected value of the next state is the step kernel's average of `v`. -/
lemma integral_mdpNextValue_step (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (v : Fin S → ℝ) (n : ℕ) (h : MDPTrajectory S A n) :
    ∫ p, v p.1 ∂(mdpStepKernel M μ0 π n h) = mdpNextValue M μ0 v n h := by
  rw [mdp_integral_stepKernel, mdpNextValue]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s ↦ by simp)


/-- Indicator of the event that none of the first `k` states of the trajectory
is the target state: on a trajectory of `n` rounds this is `1` exactly when the
hitting time of `tgt` exceeds `k`. -/
def avoidPre (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (k : ℕ) : ℝ :=
  if ∀ t : Fin n, (t : ℕ) < k → (h t).1 ≠ tgt then 1 else 0

lemma avoidPre_nonneg (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (k : ℕ) :
    0 ≤ avoidPre tgt h k := by
  unfold avoidPre; split <;> norm_num

lemma avoidPre_le_one (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (k : ℕ) :
    avoidPre tgt h k ≤ 1 := by
  unfold avoidPre; split <;> norm_num

@[simp] lemma avoidPre_zero (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) :
    avoidPre tgt h 0 = 1 := by
  unfold avoidPre
  rw [if_pos]
  exact fun t ht ↦ absurd ht (Nat.not_lt_zero _)

lemma avoidPre_snoc_of_le (tgt : Fin S) {n k : ℕ} (hk : k ≤ n)
    (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    avoidPre tgt (Fin.snoc h p) k = avoidPre tgt h k := by
  unfold avoidPre
  refine if_congr ⟨fun H t ht ↦ ?_, fun H t ht ↦ ?_⟩ rfl rfl
  · have := H t.castSucc (by simpa using ht)
    rwa [Fin.snoc_castSucc] at this
  · have htn : (t : ℕ) < n := lt_of_lt_of_le ht hk
    have : t = (Fin.castLT t htn).castSucc := by ext; simp
    rw [this, Fin.snoc_castSucc]
    exact H _ (by simpa using ht)

lemma avoidPre_snoc_succ (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n)
    (p : Fin S × Fin A) :
    avoidPre tgt (Fin.snoc h p) (n + 1)
      = avoidPre tgt h n * (if p.1 = tgt then 0 else 1) := by
  have hiff : (∀ t : Fin (n + 1), (t : ℕ) < n + 1 →
        ((Fin.snoc (α := fun _ ↦ Fin S × Fin A) h p) t).1 ≠ tgt)
      ↔ ((∀ t : Fin n, (t : ℕ) < n → (h t).1 ≠ tgt) ∧ p.1 ≠ tgt) := by
    constructor
    · intro H
      refine ⟨fun t ht ↦ ?_, ?_⟩
      · have := H t.castSucc (by simpa using t.2)
        rwa [Fin.snoc_castSucc] at this
      · have := H (Fin.last n) (by simp)
        rwa [Fin.snoc_last] at this
    · rintro ⟨H1, H2⟩ t _
      rcases Fin.eq_castSucc_or_eq_last t with ⟨t', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]; exact H1 t' t'.2
      · rwa [Fin.snoc_last]
  unfold avoidPre
  by_cases hp : p.1 = tgt
  · rw [if_neg (fun H ↦ (hiff.mp H).2 hp), if_pos hp, mul_zero]
  · rw [if_neg hp, mul_one]
    exact if_congr (hiff.trans ⟨fun H ↦ H.1, fun H ↦ ⟨H, hp⟩⟩) rfl rfl

/-- The reward accumulated strictly before the hitting time of `tgt`, measured
against the gain `ρ`: the summand of round `t` is kept only while the target has
not yet been visited. -/
noncomputable def stoppedSum (M : FiniteMDP S A) (tgt : Fin S) (ρ : ℝ) {n : ℕ}
    (h : MDPTrajectory S A n) : ℝ :=
  ∑ t : Fin n, avoidPre tgt h ((t : ℕ) + 1) * (M.r (h t).1 (h t).2 - ρ)

lemma stoppedSum_snoc (M : FiniteMDP S A) (tgt : Fin S) (ρ : ℝ) {n : ℕ}
    (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    stoppedSum M tgt ρ (Fin.snoc h p)
      = stoppedSum M tgt ρ h
        + avoidPre tgt h n * (if p.1 = tgt then 0 else 1) * (M.r p.1 p.2 - ρ) := by
  rw [stoppedSum, Fin.sum_univ_castSucc, stoppedSum]
  congr 1
  · refine Finset.sum_congr rfl fun t _ ↦ ?_
    have hk : (t : ℕ) + 1 ≤ n := t.2
    rw [Fin.coe_castSucc, avoidPre_snoc_of_le tgt hk h p, Fin.snoc_castSucc]
  · rw [Fin.val_last, Fin.snoc_last, avoidPre_snoc_succ]

/-- **The Bellman inequality accumulates up to the hitting time.**  The value of
the current state, relative to the target state, dominates the reward collected
before the target is reached (measured against `ρ`). -/
lemma stopped_bellman_le (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (tgt : Fin S) (ρ : ℝ) (v : Fin S → ℝ)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s) (n : ℕ) :
    ∫ h, (avoidPre tgt h n * (mdpNextValue M μ0 v n h - v tgt) + stoppedSum M tgt ρ h)
        ∂(mdpMeasure M μ0 π n)
      ≤ (∫ s, v s ∂μ0.toMeasure) - v tgt := by
  induction n with
  | zero =>
      rw [mdpMeasure, integral_dirac]
      simp [stoppedSum, mdpNextValue, mdpStateKernel]
  | succ n ih =>
      have key : ∀ h : MDPTrajectory S A n,
          (∫ p, (avoidPre tgt (Fin.snoc h p) (n + 1)
                  * (mdpNextValue M μ0 v (n + 1) (Fin.snoc h p) - v tgt)
                + stoppedSum M tgt ρ (Fin.snoc h p))
              ∂(mdpStepKernel M μ0 π n h))
            ≤ avoidPre tgt h n * (mdpNextValue M μ0 v n h - v tgt)
              + stoppedSum M tgt ρ h := by
        intro h
        have hpt : ∀ p : Fin S × Fin A,
            avoidPre tgt (Fin.snoc h p) (n + 1)
                  * (mdpNextValue M μ0 v (n + 1) (Fin.snoc h p) - v tgt)
                + stoppedSum M tgt ρ (Fin.snoc h p)
              ≤ stoppedSum M tgt ρ h + avoidPre tgt h n * (v p.1 - v tgt) := by
          intro p
          rw [avoidPre_snoc_succ, mdpNextValue_succ, stoppedSum_snoc]
          by_cases hp : p.1 = tgt
          · rw [if_pos hp, hp]
            simp
          · rw [if_neg hp, mul_one]
            have hb := hbell p.1 p.2
            have hnn := avoidPre_nonneg tgt h n
            nlinarith [hnn, hb]
        calc (∫ p, (avoidPre tgt (Fin.snoc h p) (n + 1)
                    * (mdpNextValue M μ0 v (n + 1) (Fin.snoc h p) - v tgt)
                  + stoppedSum M tgt ρ (Fin.snoc h p))
                ∂(mdpStepKernel M μ0 π n h))
            ≤ ∫ p, (stoppedSum M tgt ρ h + avoidPre tgt h n * (v p.1 - v tgt))
                ∂(mdpStepKernel M μ0 π n h) :=
              integral_mono Integrable.of_finite Integrable.of_finite hpt
          _ = avoidPre tgt h n * (mdpNextValue M μ0 v n h - v tgt)
                + stoppedSum M tgt ρ h := by
              rw [integral_add Integrable.of_finite Integrable.of_finite,
                integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
              have : ∫ p, avoidPre tgt h n * (v p.1 - v tgt)
                  ∂(mdpStepKernel M μ0 π n h)
                  = avoidPre tgt h n * (mdpNextValue M μ0 v n h - v tgt) := by
                rw [integral_const_mul]
                congr 1
                rw [integral_sub Integrable.of_finite Integrable.of_finite,
                  integral_mdpNextValue_step, integral_const, measureReal_univ_eq_one,
                  smul_eq_mul, one_mul]
              rw [this]
              ring
      calc ∫ h, (avoidPre tgt h (n + 1) * (mdpNextValue M μ0 v (n + 1) h - v tgt)
              + stoppedSum M tgt ρ h) ∂(mdpMeasure M μ0 π (n + 1))
          = ∫ h, (∫ p, (avoidPre tgt (Fin.snoc h p) (n + 1)
                  * (mdpNextValue M μ0 v (n + 1) (Fin.snoc h p) - v tgt)
                + stoppedSum M tgt ρ (Fin.snoc h p))
              ∂(mdpStepKernel M μ0 π n h)) ∂(mdpMeasure M μ0 π n) :=
            BanditAlgorithm.mdp_integral_trajectory_succ _ _ _ _ _
        _ ≤ ∫ h, (avoidPre tgt h n * (mdpNextValue M μ0 v n h - v tgt)
              + stoppedSum M tgt ρ h) ∂(mdpMeasure M μ0 π n) :=
            integral_mono Integrable.of_finite Integrable.of_finite key
        _ ≤ (∫ s, v s ∂μ0.toMeasure) - v tgt := ih

/-- The event that the target state is not visited during the first `n` rounds. -/
def avoidSet (tgt : Fin S) (n : ℕ) : Set (MDPTrajectory S A n) :=
  {h | ∀ t, (h t).1 ≠ tgt}

lemma avoidPre_self (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) :
    avoidPre tgt h n = Set.indicator (avoidSet tgt n) 1 h := by
  by_cases hc : h ∈ avoidSet tgt n
  · rw [Set.indicator_of_mem hc]
    unfold avoidPre
    rw [if_pos (fun t _ ↦ hc t)]
    rfl
  · rw [Set.indicator_of_notMem hc]
    unfold avoidPre
    rw [if_neg]
    exact fun H ↦ hc fun t ↦ H t t.2

lemma avoidPre_restrict (tgt : Fin S) {m n k : ℕ} (hmn : m ≤ n) (hk : k ≤ m)
    (h : MDPTrajectory S A n) :
    avoidPre tgt (mdpRestrict hmn h) k = avoidPre tgt h k := by
  unfold avoidPre mdpRestrict
  refine if_congr ⟨fun H t ht ↦ ?_, fun H t ht ↦ ?_⟩ rfl rfl
  · have htm : (t : ℕ) < m := lt_of_lt_of_le ht hk
    have := H ⟨t, htm⟩ ht
    simpa [Fin.castLE] using this
  · have := H (Fin.castLE hmn t) (by simpa using ht)
    simpa using this

/-- The expectation of the avoidance indicator is the probability of the event,
computed at the horizon where the event lives. -/
lemma integral_avoidPre (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (tgt : Fin S) {k n : ℕ} (hk : k ≤ n) :
    ∫ h, avoidPre tgt h k ∂(mdpMeasure M μ0 π n)
      = (mdpMeasure M μ0 π k (avoidSet tgt k)).toReal := by
  have hfun : (fun h : MDPTrajectory S A n ↦ avoidPre tgt h k)
      = (fun g : MDPTrajectory S A k ↦ avoidPre tgt g k) ∘ (mdpRestrict hk) := by
    funext h
    exact (avoidPre_restrict tgt hk le_rfl h).symm
  rw [hfun]
  simp only [Function.comp_def]
  have hmap := integral_map (μ := mdpMeasure M μ0 π n) (φ := mdpRestrict hk)
      (f := fun g : MDPTrajectory S A k ↦ avoidPre tgt g k)
      (measurable_mdpRestrict hk).aemeasurable (Integrable.of_finite).aestronglyMeasurable
  have hres : (mdpMeasure M μ0 π n).map (mdpRestrict hk) = mdpMeasure M μ0 π k :=
    BanditAlgorithm.mdp_measure_map_restrict M μ0 π hk
  rw [hres] at hmap
  rw [← hmap]
  have : (fun g : MDPTrajectory S A k ↦ avoidPre tgt g k)
      = Set.indicator (avoidSet tgt k) 1 := by
    funext g; exact avoidPre_self tgt g
  rw [this, integral_indicator_one (MeasurableSet.of_discrete), measureReal_def]


theorem solution (M : FiniteMDP S A) (f : Fin S → Fin A)
    (src tgt : Fin S) (ρ : ℝ) (v : Fin S → ℝ) (lo hi : ℝ)
    (hv : ∀ s, v s ∈ Set.Icc lo hi)
    (hbell : ∀ s a, M.r s a + ∑ s', (M.P s a s' : ℝ) * v s' ≤ ρ + v s)
    (hfin : mdpTravelTime M f src tgt ≠ ⊤) :
    v tgt - v src ≤ ρ * (mdpTravelTime M f src tgt).toReal := by
  set μ0 := mdpStateDirac src with hμ0
  set π := mdpMemorylessDetPolicy f with hπ
  set a : ℕ → ℝ≥0∞ := fun k ↦ mdpMeasure M μ0 π (k + 1) (avoidSet tgt (k + 1)) with ha
  have htt : mdpTravelTime M f src tgt = ∑' k, a k := rfl
  have hane : ∀ k, a k ≠ ⊤ := fun k ↦ measure_ne_top _ _
  have hsum : Summable (fun k ↦ (a k).toReal) := ENNReal.summable_toReal (by rwa [← htt])
  have htsum : ∑' k, (a k).toReal = (mdpTravelTime M f src tgt).toReal := by
    rw [htt, ENNReal.tsum_toReal_eq hane]
  -- the initial value is the value of the starting state
  have hinit : ∫ s, v s ∂μ0.toMeasure = v src := by
    rw [integral_mdpStateDistribution]
    rw [Finset.sum_eq_single src]
    · simp [hμ0, mdpStateDirac]
    · intro b _ hb; simp [hμ0, mdpStateDirac, hb]
    · simp
  -- the per-horizon inequality
  have hstep : ∀ k : ℕ, v tgt - v src
      ≤ (hi - lo) * (a k).toReal + ρ * ∑ t ∈ Finset.range (k + 1), (a t).toReal := by
    intro k
    have hmain := stopped_bellman_le M μ0 π tgt ρ v hbell (k + 1)
    rw [hinit] at hmain
    -- lower bound the first part
    have h1 : ∀ h : MDPTrajectory S A (k + 1),
        (lo - hi) * avoidPre tgt h (k + 1)
          ≤ avoidPre tgt h (k + 1) * (mdpNextValue M μ0 v (k + 1) h - v tgt) := by
      intro h
      have hnv : lo ≤ mdpNextValue M μ0 v (k + 1) h := by
        calc lo = ∫ _s, lo ∂(mdpStateKernel M μ0 (k + 1) h) := by
              rw [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
          _ ≤ _ := integral_mono Integrable.of_finite Integrable.of_finite fun s ↦ (hv s).1
      have := avoidPre_nonneg tgt h (k + 1)
      nlinarith [(hv tgt).2]
    -- lower bound the accumulated reward
    have h2 : ∀ h : MDPTrajectory S A (k + 1),
        (-ρ) * ∑ t : Fin (k + 1), avoidPre tgt h ((t : ℕ) + 1)
          ≤ stoppedSum M tgt ρ h := by
      intro h
      rw [stoppedSum, Finset.mul_sum]
      refine Finset.sum_le_sum fun t _ ↦ ?_
      have hr := (M.r_mem_Icc (h t).1 (h t).2).1
      have hnn := avoidPre_nonneg tgt h ((t : ℕ) + 1)
      nlinarith
    have hlow : ∀ h : MDPTrajectory S A (k + 1),
        (lo - hi) * avoidPre tgt h (k + 1)
            + (-ρ) * ∑ t : Fin (k + 1), avoidPre tgt h ((t : ℕ) + 1)
          ≤ avoidPre tgt h (k + 1) * (mdpNextValue M μ0 v (k + 1) h - v tgt)
            + stoppedSum M tgt ρ h := fun h ↦ add_le_add (h1 h) (h2 h)
    have hint := le_trans (integral_mono Integrable.of_finite Integrable.of_finite hlow)
      hmain
    rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul,
      integral_const_mul, integral_avoidPre M μ0 π tgt (le_refl (k + 1))] at hint
    have hsplit : ∫ h, (∑ t : Fin (k + 1), avoidPre tgt h ((t : ℕ) + 1))
          ∂(mdpMeasure M μ0 π (k + 1))
        = ∑ t ∈ Finset.range (k + 1), (a t).toReal := by
      rw [integral_finset_sum _ (fun t _ ↦ Integrable.of_finite)]
      rw [← Fin.sum_univ_eq_sum_range (fun t ↦ (a t).toReal)]
      refine Finset.sum_congr rfl fun t _ ↦ ?_
      exact integral_avoidPre M μ0 π tgt (Nat.succ_le_of_lt t.2)
    rw [hsplit] at hint
    have : a k = mdpMeasure M μ0 π (k + 1) (avoidSet tgt (k + 1)) := rfl
    rw [← this] at hint
    linarith
  -- pass to the limit
  have hlim : Filter.Tendsto
      (fun k ↦ (hi - lo) * (a k).toReal + ρ * ∑ t ∈ Finset.range (k + 1), (a t).toReal)
      Filter.atTop (nhds ((hi - lo) * 0 + ρ * (mdpTravelTime M f src tgt).toReal)) := by
    refine Filter.Tendsto.add (tendsto_const_nhds.mul hsum.tendsto_atTop_zero)
      (tendsto_const_nhds.mul ?_)
    rw [← htsum]
    exact (hsum.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have := ge_of_tendsto hlim (Filter.Eventually.of_forall hstep)
  linarith [this]

