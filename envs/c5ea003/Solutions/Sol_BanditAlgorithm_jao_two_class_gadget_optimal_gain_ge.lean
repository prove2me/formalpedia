-- Prove2me | solution 1 for BanditAlgorithm.jao_two_class_gadget_optimal_gain_ge
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T03:57:37.494258+00:00
-- url     : https://prove2.me/submissions/bb91b84f-2bf7-4a0c-8ef2-c5b7921b9ccd

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Order.LiminfLimsup
import Definitions.Def_FiniteMDPLearning
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoGainC

variable {S A : ℕ}

lemma toMeasure_apply (d : MDPStateDistribution S) (B : Set (Fin S)) :
    d.toMeasure B = ∑ i, (d.prob i : ℝ≥0∞) * B.indicator 1 i := by
  rw [MDPStateDistribution.toMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma toMeasure_real_singleton (d : MDPStateDistribution S) (s : Fin S) :
    (d.toMeasure).real {s} = (d.prob s : ℝ) := by
  rw [measureReal_def, toMeasure_apply, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

lemma integral_fin (d : MDPStateDistribution S) (g : Fin S → ℝ) :
    (∫ t, g t ∂d.toMeasure) = ∑ t, (d.prob t : ℝ) * g t := by
  rw [integral_fintype (by exact Integrable.of_finite)]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [toMeasure_real_singleton, smul_eq_mul]

/-- A distribution whose mass at two distinct points already sums to one is
supported on those two points. -/
lemma integral_two_point (d : MDPStateDistribution S) (u v : Fin S) (huv : u ≠ v)
    (hsum : (d.prob u : ℝ) + (d.prob v : ℝ) = 1) (g : Fin S → ℝ) :
    (∫ t, g t ∂d.toMeasure) = (d.prob u : ℝ) * g u + (d.prob v : ℝ) * g v := by
  classical
  have htot : ∑ t, (d.prob t : ℝ) = 1 := by
    have h1 := d.sum_one
    have h2 : ((∑ t, d.prob t : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [h1]
    simpa using h2
  set P : Finset (Fin S) := {u, v} with hP
  have hpair : ∑ t ∈ P, (d.prob t : ℝ) = 1 := by
    rw [hP, Finset.sum_pair huv, hsum]
  have hrest : ∑ t ∈ Finset.univ \ P, (d.prob t : ℝ) = 0 := by
    have hsplit := Finset.sum_sdiff (f := fun t ↦ (d.prob t : ℝ)) (Finset.subset_univ P)
    rw [hpair, htot] at hsplit
    linarith
  have hzero : ∀ t ∈ Finset.univ \ P, (d.prob t : ℝ) = 0 := by
    intro t ht
    by_contra hne
    have hpos : 0 < (d.prob t : ℝ) := lt_of_le_of_ne (d.prob t).coe_nonneg (Ne.symm hne)
    have : 0 < ∑ x ∈ Finset.univ \ P, (d.prob x : ℝ) :=
      Finset.sum_pos' (fun x _ ↦ (d.prob x).coe_nonneg) ⟨t, ht, hpos⟩
    linarith [hrest]
  rw [integral_fin, ← Finset.sum_sdiff (Finset.subset_univ P)]
  rw [Finset.sum_eq_zero (fun t ht ↦ by rw [hzero t ht]; ring)]
  rw [hP, Finset.sum_pair huv]
  ring

lemma integral_nonneg_dist (d : MDPStateDistribution S) (g : Fin S → ℝ)
    (hg : ∀ t, 0 ≤ g t) : 0 ≤ ∫ t, g t ∂d.toMeasure := by
  rw [integral_fin]
  exact Finset.sum_nonneg fun t _ ↦ mul_nonneg (d.prob t).coe_nonneg (hg t)

lemma integral_state_zero (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 0 h)) = ∫ s, g s ∂μ0.toMeasure := by
  rw [mdpStateKernel]; simp

lemma integral_state_succ {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A (n + 1)) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 (n + 1) h))
      = ∫ s, g s ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply]; rfl

/-- Under a memoryless deterministic policy the action of the step kernel is read
off the state, so a function of the pair becomes a function of the state alone. -/
lemma integral_step_det {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (f : Fin S → Fin A) (h : MDPTrajectory S A n) (g : Fin S × Fin A → ℝ) :
    (∫ p, g p ∂(mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h))
      = ∫ s, g (s, f s) ∂(mdpStateKernel M μ0 n h) := by
  rw [mdpStepKernel, ProbabilityTheory.integral_compProd (by exact Integrable.of_finite)]
  have hsel : ∀ s : Fin S,
      (∫ b, g (s, b) ∂((mdpMemorylessDetPolicy f).select n (h, s))) = g (s, f s) := by
    intro s
    rw [mdpMemorylessDetPolicy]
    simp only [Kernel.deterministic_apply]
    rw [integral_dirac]
  simp_rw [hsel]

/-- `W M f s₀ g n` is the expectation of `g` at the state-action pair of round
`n + 1`, under the memoryless deterministic policy `f` started from `s₀`. -/
noncomputable def W (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    (g : Fin S × Fin A → ℝ) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, g p ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n h))
    ∂(mdpMeasure M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n)

lemma W_zero (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    (g : Fin S × Fin A → ℝ) : W M f s₀ g 0 = g (s₀, f s₀) := by
  have hz : ∀ h : MDPTrajectory S A 0,
      (∫ p, g p ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) 0 h))
        = g (s₀, f s₀) := by
    intro h
    rw [integral_step_det, integral_state_zero, integral_fin, Finset.sum_eq_single s₀]
    · simp [mdpStateDirac]
    · intro b _ hb
      simp [mdpStateDirac, hb]
    · intro hcon
      exact absurd (Finset.mem_univ s₀) hcon
  rw [W]
  simp [hz]

/-- One step: the expectation of `g` at round `n + 2` is the expectation at round
`n + 1` of the one-step average of `g` along the transition row. -/
lemma W_succ (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    (g : Fin S × Fin A → ℝ) (n : ℕ) :
    W M f s₀ g (n + 1)
      = W M f s₀ (fun p ↦ ∫ t, g (t, f t) ∂(M.transitionDist p.1 p.2).toMeasure) n := by
  have hinner : ∀ h : MDPTrajectory S A (n + 1),
      (∫ p, g p ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) (n + 1) h))
        = (fun p : Fin S × Fin A ↦
            ∫ t, g (t, f t) ∂(M.transitionDist p.1 p.2).toMeasure) (h (Fin.last n)) := by
    intro h
    rw [integral_step_det, integral_state_succ]
  rw [W]
  simp_rw [hinner]
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀)
    (mdpMemorylessDetPolicy f) n
    (fun h' ↦ (fun p : Fin S × Fin A ↦
      ∫ t, g (t, f t) ∂(M.transitionDist p.1 p.2).toMeasure) (h' (Fin.last n))), W]
  simp

lemma W_mono (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    {g g' : Fin S × Fin A → ℝ} (hle : ∀ p, g p ≤ g' p) (n : ℕ) :
    W M f s₀ g n ≤ W M f s₀ g' n := by
  rw [W, W]
  refine integral_mono (by exact Integrable.of_finite) (by exact Integrable.of_finite) ?_
  intro h
  exact integral_mono (by exact Integrable.of_finite) (by exact Integrable.of_finite)
    fun p ↦ hle p

lemma W_add_smul (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    (α β : ℝ) (g g' : Fin S × Fin A → ℝ) (n : ℕ) :
    W M f s₀ (fun p ↦ α * g p + β * g' p) n = α * W M f s₀ g n + β * W M f s₀ g' n := by
  have hin : ∀ h : MDPTrajectory S A n,
      (∫ p, (α * g p + β * g' p)
          ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n h))
        = α * (∫ p, g p ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n h))
          + β * ∫ p, g' p
              ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n h) := by
    intro h
    rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
      integral_const_mul, integral_const_mul]
  rw [W]
  simp_rw [hin]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
    integral_const_mul, integral_const_mul, W, W]

/-- The reward accumulated over `n` rounds. -/
noncomputable def R (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S) (n : ℕ) : ℝ :=
  ∫ h, mdpTrajectoryReward M h
    ∂(mdpMeasure M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n)

lemma reward_snoc (ρ : Fin S → ℝ) (M : FiniteMDP S A) (hr : ∀ s b, M.r s b = ρ s)
    {n : ℕ} (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + ρ p.1 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro t _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last, hr]

lemma R_zero (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S) : R M f s₀ 0 = 0 := by
  rw [R]
  have hz : ∀ h : MDPTrajectory S A 0, mdpTrajectoryReward M h = 0 := by
    intro h; rw [mdpTrajectoryReward]; simp
  simp [hz]

lemma R_succ (ρ : Fin S → ℝ) (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    (hr : ∀ s b, M.r s b = ρ s) (n : ℕ) :
    R M f s₀ (n + 1) = R M f s₀ n + W M f s₀ (fun p ↦ ρ p.1) n := by
  rw [R, BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀)
    (mdpMemorylessDetPolicy f) n (fun h' ↦ mdpTrajectoryReward M h')]
  simp_rw [reward_snoc ρ M hr]
  have hin : ∀ h : MDPTrajectory S A n,
      (∫ p, (mdpTrajectoryReward M h + ρ p.1)
          ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n h))
        = mdpTrajectoryReward M h
            + ∫ p, ρ p.1
                ∂(mdpStepKernel M (mdpStateDirac s₀) (mdpMemorylessDetPolicy f) n h) := by
    intro h
    rw [integral_add (integrable_const _) (by exact Integrable.of_finite), integral_const]
    simp
  simp_rw [hin]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite), R, W]

lemma R_eq_sum (ρ : Fin S → ℝ) (M : FiniteMDP S A) (f : Fin S → Fin A) (s₀ : Fin S)
    (hr : ∀ s b, M.r s b = ρ s) (T : ℕ) :
    R M f s₀ T = ∑ n ∈ Finset.range T, W M f s₀ (fun p ↦ ρ p.1) n := by
  induction T with
  | zero => rw [R_zero]; simp
  | succ T ih => rw [R_succ ρ M f s₀ hr T, ih, Finset.sum_range_succ]

/-- The indicator that the state of the pair is `u`. -/
def indState (u : Fin S) : Fin S × Fin A → ℝ := fun p ↦ if p.1 = u then 1 else 0

/-- The indicator that the pair is `q`. -/
def indPair (q : Fin S × Fin A) : Fin S × Fin A → ℝ := fun p ↦ if p = q then 1 else 0

lemma indState_nonneg (u : Fin S) (p : Fin S × Fin A) : 0 ≤ indState u p := by
  simp only [indState]; split_ifs <;> norm_num

lemma indPair_nonneg (q p : Fin S × Fin A) : 0 ≤ indPair q p := by
  simp only [indPair]; split_ifs <;> norm_num

lemma indPair_snd (sStar : Fin S) (bStar : Fin A) (t : Fin S) :
    indPair (sStar, bStar) (t, bStar) = if t = sStar then 1 else 0 := by
  simp only [indPair]
  by_cases h : t = sStar
  · simp [h]
  · rw [if_neg h, if_neg (fun hc ↦ h (congrArg Prod.fst hc))]

section Gadget

variable (δ ε : ℝ) (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
  (sStar : Fin S) (bStar : Fin A) (M : FiniteMDP S A)

/-- The one-step inequality for the rewarding-state indicator, valid at **every**
state-action pair: it is an equality on the two states of the confined chain, and
its left side vanishes elsewhere. -/
lemma step_state
    (hstar : ρ sStar = 0) (hfix : nav sStar bStar = sStar)
    (hud : down (up sStar) = sStar) (hup1 : ρ (up sStar) = 1) (hne : sStar ≠ up sStar)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ)
    (s : Fin S) (b : Fin A) :
    (δ + ε) * indPair (sStar, bStar) (s, b) + (1 - δ) * indState (up sStar) (s, b)
      ≤ ∫ t, indState (up sStar) (t, bStar) ∂(M.transitionDist s b).toMeasure := by
  classical
  have hp : ∀ (s' : Fin S) (b' : Fin A) (t : Fin S),
      (((M.transitionDist s' b').prob t : ℝ)) = ((M.P s' b' t : ℝ)) := fun _ _ _ ↦ rfl
  by_cases hq : ((s, b) : Fin S × Fin A) = (sStar, bStar)
  · obtain ⟨hs, hb⟩ : s = sStar ∧ b = bStar :=
      ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩
    have hρs : ρ s = 0 := by rw [hs]; exact hstar
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrow0M s b hρs
    have hnavs : nav s b = sStar := by rw [hs, hb]; exact hfix
    rw [integral_two_point _ (up s) (nav s b) h3 (by rw [hp, hp, h4, h5]; ring)]
    rw [hp, hp, h4, h5, hnavs]
    simp only [if_pos hq]
    simp [indState, indPair, hq, hs, hb, hne, Ne.symm hne]
  · by_cases hu : s = up sStar
    · have hρs : ρ s = 1 := by rw [hu]; exact hup1
      obtain ⟨h1, h2, h3, h4⟩ := hrow1M s b hρs
      have hds : down s = sStar := by rw [hu]; exact hud
      rw [integral_two_point _ (down s) s h2 (by rw [hp, hp, h3, h4]; ring)]
      rw [hp, hp, h3, h4, hds]
      simp [indState, indPair, hq, hu, hne, Ne.symm hne]
    · have hz1 : indPair (sStar, bStar) (s, b) = 0 := by simp only [indPair]; exact if_neg hq
      have hz2 : indState (up sStar) (s, b) = 0 := by simp only [indState]; exact if_neg hu
      rw [hz1, hz2]
      have := integral_nonneg_dist (M.transitionDist s b)
        (fun t ↦ indState (up sStar) (t, bStar)) (fun t ↦ indState_nonneg _ _)
      linarith

/-- The one-step inequality for the planted-pair indicator. -/
lemma step_pair
    (hstar : ρ sStar = 0) (hfix : nav sStar bStar = sStar)
    (hud : down (up sStar) = sStar) (hup1 : ρ (up sStar) = 1) (hne : sStar ≠ up sStar)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ)
    (s : Fin S) (b : Fin A) :
    (1 - δ - ε) * indPair (sStar, bStar) (s, b) + δ * indState (up sStar) (s, b)
      ≤ ∫ t, indPair (sStar, bStar) (t, bStar) ∂(M.transitionDist s b).toMeasure := by
  classical
  have hp : ∀ (s' : Fin S) (b' : Fin A) (t : Fin S),
      (((M.transitionDist s' b').prob t : ℝ)) = ((M.P s' b' t : ℝ)) := fun _ _ _ ↦ rfl
  simp_rw [indPair_snd sStar bStar]
  by_cases hq : ((s, b) : Fin S × Fin A) = (sStar, bStar)
  · obtain ⟨hs, hb⟩ : s = sStar ∧ b = bStar :=
      ⟨congrArg Prod.fst hq, congrArg Prod.snd hq⟩
    have hρs : ρ s = 0 := by rw [hs]; exact hstar
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrow0M s b hρs
    have hnavs : nav s b = sStar := by rw [hs, hb]; exact hfix
    rw [integral_two_point _ (up s) (nav s b) h3 (by rw [hp, hp, h4, h5]; ring)]
    rw [hp, hp, h4, h5, hnavs]
    simp only [if_pos hq]
    simp [indState, indPair, hq, hs, hb, hne, Ne.symm hne]
  · by_cases hu : s = up sStar
    · have hρs : ρ s = 1 := by rw [hu]; exact hup1
      obtain ⟨h1, h2, h3, h4⟩ := hrow1M s b hρs
      have hds : down s = sStar := by rw [hu]; exact hud
      rw [integral_two_point _ (down s) s h2 (by rw [hp, hp, h3, h4]; ring)]
      rw [hp, hp, h3, h4, hds]
      simp [indState, indPair, hq, hu, hne, Ne.symm hne]
    · have hz1 : indPair (sStar, bStar) (s, b) = 0 := by simp only [indPair]; exact if_neg hq
      have hz2 : indState (up sStar) (s, b) = 0 := by simp only [indState]; exact if_neg hu
      rw [hz1, hz2]
      have hnn : (0 : ℝ) ≤ ∫ t, (if t = sStar then (1 : ℝ) else 0)
          ∂(M.transitionDist s b).toMeasure := by
        refine integral_nonneg_dist (M.transitionDist s b) _ ?_
        intro t
        split_ifs <;> norm_num
      linarith

end Gadget

end JaoGainC

open JaoGainC

theorem solution {S A : ℕ}
    (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (sStar : Fin S) (bStar : Fin A) (M : FiniteMDP S A)
    (hstar : ρ sStar = 0) (hfix : nav sStar bStar = sStar)
    (hud : down (up sStar) = sStar)
    (hrM : ∀ s b, M.r s b = ρ s)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ) :
    (δ + ε) / (2 * δ + ε) ≤ mdpOptimalGain M := by
  classical
  have hden : (0 : ℝ) < 2 * δ + ε := by linarith
  set g : ℝ := (δ + ε) / (2 * δ + ε) with hg
  set c : ℝ := 1 - 2 * δ - ε with hc
  have hc0 : (0 : ℝ) ≤ c := by rw [hc]; linarith
  have hc1 : c < 1 := by rw [hc]; linarith
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hg0 : (0 : ℝ) ≤ g := by rw [hg]; positivity
  have hgc : g * (1 - c) = δ + ε := by
    have h1 : (1 : ℝ) - c = 2 * δ + ε := by rw [hc]; ring
    rw [h1, hg]
    field_simp
  -- `ρ` takes values in `[0,1]`, being the reward
  have hρ0 : ∀ s, 0 ≤ ρ s := by
    intro s
    have h := M.r_mem_Icc s bStar
    rw [hrM] at h
    exact h.1
  have hup1 : ρ (up sStar) = 1 := (hrow0M sStar bStar hstar).1
  have hne : sStar ≠ up sStar := by
    intro hcon
    rw [← hcon, hstar] at hup1
    norm_num at hup1
  set f : Fin S → Fin A := fun _ ↦ bStar with hf
  -- the two pointwise one-step inequalities
  have hstep := step_state δ ε ρ up down nav sStar bStar M hstar hfix hud hup1 hne hrow0M hrow1M
  have hstepP := step_pair δ ε ρ up down nav sStar bStar M hstar hfix hud hup1 hne hrow0M hrow1M
  -- the two occupancy sequences dominate the stationary recursion
  have hkey : ∀ n : ℕ,
      g * (1 - c ^ n) ≤ W M f sStar (indState (up sStar)) n
        ∧ 1 - g * (1 - c ^ n) ≤ W M f sStar (indPair (sStar, bStar)) n := by
    intro n
    induction n with
    | zero =>
        constructor
        · rw [W_zero]
          simp only [pow_zero, sub_self, mul_zero]
          exact indState_nonneg _ _
        · rw [W_zero]
          simp only [pow_zero, sub_self, mul_zero, sub_zero]
          rw [hf, indPair]
          simp
    | succ n ih =>
        obtain ⟨ih1, ih2⟩ := ih
        have hrec1 : (δ + ε) * W M f sStar (indPair (sStar, bStar)) n
            + (1 - δ) * W M f sStar (indState (up sStar)) n
            ≤ W M f sStar (indState (up sStar)) (n + 1) := by
          rw [W_succ]
          have hmono := W_mono M f sStar
            (g := fun p ↦ (δ + ε) * indPair (sStar, bStar) p
              + (1 - δ) * indState (up sStar) p)
            (g' := fun p ↦ ∫ t, indState (up sStar) (t, f t)
              ∂(M.transitionDist p.1 p.2).toMeasure)
            (fun p ↦ hstep p.1 p.2) n
          rw [W_add_smul] at hmono
          exact hmono
        have hrec2 : (1 - δ - ε) * W M f sStar (indPair (sStar, bStar)) n
            + δ * W M f sStar (indState (up sStar)) n
            ≤ W M f sStar (indPair (sStar, bStar)) (n + 1) := by
          rw [W_succ]
          have hmono := W_mono M f sStar
            (g := fun p ↦ (1 - δ - ε) * indPair (sStar, bStar) p
              + δ * indState (up sStar) p)
            (g' := fun p ↦ ∫ t, indPair (sStar, bStar) (t, f t)
              ∂(M.transitionDist p.1 p.2).toMeasure)
            (fun p ↦ hstepP p.1 p.2) n
          rw [W_add_smul] at hmono
          exact hmono
        have hcv : (1 : ℝ) - 2 * δ - ε = c := hc.symm
        have hstep1 : g * (1 - c ^ (n + 1))
            = (δ + ε) * (1 - g * (1 - c ^ n)) + (1 - δ) * (g * (1 - c ^ n)) := by
          have hcp : c ^ (n + 1) = c * c ^ n := by ring
          calc g * (1 - c ^ (n + 1)) = g * (1 - c) + c * (g * (1 - c ^ n)) := by
                rw [hcp]; ring
            _ = (δ + ε) + c * (g * (1 - c ^ n)) := by rw [hgc]
            _ = (δ + ε) * (1 - g * (1 - c ^ n)) + (1 - δ) * (g * (1 - c ^ n)) := by
                rw [← hcv]; ring
        have hstep2 : 1 - g * (1 - c ^ (n + 1))
            = (1 - δ - ε) * (1 - g * (1 - c ^ n)) + δ * (g * (1 - c ^ n)) := by
          rw [hstep1]; ring
        constructor
        · rw [hstep1]
          have hA : (δ + ε) * (1 - g * (1 - c ^ n))
              ≤ (δ + ε) * W M f sStar (indPair (sStar, bStar)) n :=
            mul_le_mul_of_nonneg_left ih2 (by linarith)
          have hB : (1 - δ) * (g * (1 - c ^ n))
              ≤ (1 - δ) * W M f sStar (indState (up sStar)) n :=
            mul_le_mul_of_nonneg_left ih1 (by linarith)
          linarith
        · rw [hstep2]
          have hA : (1 - δ - ε) * (1 - g * (1 - c ^ n))
              ≤ (1 - δ - ε) * W M f sStar (indPair (sStar, bStar)) n :=
            mul_le_mul_of_nonneg_left ih2 (by linarith)
          have hB : δ * (g * (1 - c ^ n))
              ≤ δ * W M f sStar (indState (up sStar)) n :=
            mul_le_mul_of_nonneg_left ih1 (by linarith)
          linarith
  -- the reward dominates the occupancy of the rewarding state
  have hrew : ∀ n : ℕ, g * (1 - c ^ n) ≤ W M f sStar (fun p ↦ ρ p.1) n := by
    intro n
    refine le_trans (hkey n).1 (W_mono M f sStar ?_ n)
    intro p
    simp only [indState]
    by_cases hpu : p.1 = up sStar
    · rw [if_pos hpu, hpu, hup1]
    · rw [if_neg hpu]
      exact hρ0 p.1
  have hRlow : ∀ n : ℕ, g * (n : ℝ) - g * ((1 - c ^ n) / (1 - c)) ≤ R M f sStar n := by
    intro n
    rw [R_eq_sum ρ M f sStar hrM n]
    have hsum : ∑ k ∈ Finset.range n, g * (1 - c ^ k)
        ≤ ∑ k ∈ Finset.range n, W M f sStar (fun p ↦ ρ p.1) k :=
      Finset.sum_le_sum fun k _ ↦ hrew k
    have hgeom : ∑ k ∈ Finset.range n, c ^ k = (1 - c ^ n) / (1 - c) := by
      rw [eq_div_iff (by linarith : (1 : ℝ) - c ≠ 0)]
      exact geom_sum_mul_neg c n
    have hval : ∑ k ∈ Finset.range n, g * (1 - c ^ k)
        = g * (n : ℝ) - g * ((1 - c ^ n) / (1 - c)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hgeom]
      ring
    linarith [hval ▸ hsum]
  -- the gain of the always-`bStar` policy from `sStar`
  set π₀ : MDPPolicy S A := mdpMemorylessDetPolicy f with hπ₀
  haveI : Nonempty (MDPPolicy S A) := ⟨π₀⟩
  have hRdef : ∀ n : ℕ, mdpExpectedReward M (mdpStateDirac sStar) π₀ n = R M f sStar n := by
    intro n; rw [mdpExpectedReward, R, hπ₀]
  -- every gain is at most one
  have hrew_le : ∀ (π : MDPPolicy S A) (s : Fin S) (n : ℕ),
      mdpExpectedReward M (mdpStateDirac s) π n ≤ n := by
    intro π s n
    rw [mdpExpectedReward]
    calc (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s) π n))
        ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M (mdpStateDirac s) π n) := by
          refine integral_mono (by exact Integrable.of_finite)
            (by exact Integrable.of_finite) ?_
          intro h
          rw [mdpTrajectoryReward]
          calc (∑ t, M.r (h t).1 (h t).2) ≤ ∑ _t : Fin n, (1 : ℝ) :=
                Finset.sum_le_sum (fun t _ ↦ (M.r_mem_Icc (h t).1 (h t).2).2)
            _ = (n : ℝ) := by simp
      _ = (n : ℝ) := by simp
  have hrew_nonneg : ∀ (π : MDPPolicy S A) (s : Fin S) (n : ℕ),
      0 ≤ mdpExpectedReward M (mdpStateDirac s) π n := by
    intro π s n
    rw [mdpExpectedReward]
    refine integral_nonneg ?_
    intro h
    rw [mdpTrajectoryReward]
    exact Finset.sum_nonneg (fun t _ ↦ (M.r_mem_Icc (h t).1 (h t).2).1)
  have hgain_le : ∀ (π : MDPPolicy S A) (s : Fin S), mdpGain M π s ≤ 1 := by
    intro π s
    rw [mdpGain]
    apply Filter.limsup_le_of_le
    · refine ⟨0, ?_⟩
      intro x hx
      rw [Filter.eventually_map] at hx
      have h1 : ∀ᶠ n : ℕ in Filter.atTop,
          (0 : ℝ) ≤ mdpExpectedReward M (mdpStateDirac s) π n / n := by
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have := hrew_nonneg π s n
        positivity
      obtain ⟨n, hn⟩ := (h1.and hx).exists
      linarith [hn.1, hn.2]
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
      rw [div_le_one hn0]
      exact hrew_le π s n
  -- the comparison sequence, which tends to `g`
  set low : ℕ → ℝ := fun n ↦ g - g / (1 - c) * ((1 - c ^ n) / n) with hlow
  have hlowle : low ≤ᶠ[Filter.atTop]
      fun n : ℕ ↦ mdpExpectedReward M (mdpStateDirac sStar) π₀ n / n := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    rw [hRdef, le_div_iff₀ hn0, hlow]
    have hexp : (g - g / (1 - c) * ((1 - c ^ n) / n)) * n
        = g * (n : ℝ) - g * ((1 - c ^ n) / (1 - c)) := by
      field_simp
    dsimp only
    rw [hexp]
    exact hRlow n
  have htend : Filter.Tendsto low Filter.atTop (nhds g) := by
    have hzero : Filter.Tendsto (fun n : ℕ ↦ (1 - c ^ n) / (n : ℝ)) Filter.atTop (nhds 0) := by
      apply squeeze_zero' (g := fun n : ℕ ↦ 1 / (n : ℝ))
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have hcn : c ^ n ≤ 1 := pow_le_one₀ hc0 hc1.le
        have : (0 : ℝ) ≤ 1 - c ^ n := by linarith
        positivity
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
        have hcn : (0 : ℝ) ≤ c ^ n := pow_nonneg hc0 n
        exact div_le_div_of_nonneg_right (by linarith) hn0.le
      · exact tendsto_one_div_atTop_nhds_zero_nat
    have h := (tendsto_const_nhds (x := g) (f := Filter.atTop (α := ℕ))).sub
      (hzero.const_mul (g / (1 - c)))
    simp only [mul_zero, sub_zero] at h
    exact h
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ ↦ mdpExpectedReward M (mdpStateDirac sStar) π₀ n / n) := by
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
    rw [div_le_one hn0]
    exact hrew_le π₀ sStar n
  have hgain : g ≤ mdpGain M π₀ sStar := by
    rw [mdpGain, ← htend.limsup_eq]
    exact Filter.limsup_le_limsup hlowle htend.isCoboundedUnder_le hbdd
  -- push through the two suprema
  calc g ≤ mdpGain M π₀ sStar := hgain
    _ ≤ ⨆ π : MDPPolicy S A, mdpGain M π sStar := by
        apply le_ciSup (f := fun π : MDPPolicy S A ↦ mdpGain M π sStar)
        exact ⟨1, by rintro x ⟨π, rfl⟩; exact hgain_le π sStar⟩
    _ ≤ mdpOptimalGain M := by
        rw [mdpOptimalGain]
        apply le_ciSup (f := fun s : Fin S ↦ ⨆ π : MDPPolicy S A, mdpGain M π s)
        refine ⟨1, ?_⟩
        rintro x ⟨s, rfl⟩
        refine ciSup_le ?_
        intro π
        exact hgain_le π s
