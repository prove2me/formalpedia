-- Prove2me | solution 1 for BanditAlgorithm.jao_two_class_reward_le_reference_plus_planted_plays_two_valued
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T03:27:47.629685+00:00
-- url     : https://prove2.me/submissions/bc41b624-72c2-4009-898f-a3dd2459e1da

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Algebra.Field.GeomSum
import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoTwoClassOcc

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
    have := d.sum_one
    have : ((∑ t, d.prob t : ℝ≥0) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [this]
    simpa using this
  set P : Finset (Fin S) := {u, v} with hP
  have hpair : ∑ t ∈ P, (d.prob t : ℝ) = 1 := by
    rw [hP, Finset.sum_pair huv, hsum]
  have hrest : ∑ t ∈ Finset.univ \ P, (d.prob t : ℝ) = 0 := by
    have hsplit := Finset.sum_sdiff (f := fun t => (d.prob t : ℝ)) (Finset.subset_univ P)
    rw [hpair, htot] at hsplit
    linarith
  have hzero : ∀ t ∈ Finset.univ \ P, (d.prob t : ℝ) = 0 := by
    intro t ht
    by_contra hne
    have hpos : 0 < (d.prob t : ℝ) := lt_of_le_of_ne (d.prob t).coe_nonneg (Ne.symm hne)
    have : 0 < ∑ x ∈ Finset.univ \ P, (d.prob x : ℝ) :=
      Finset.sum_pos' (fun x _ => (d.prob x).coe_nonneg) ⟨t, ht, hpos⟩
    linarith [hrest]
  rw [integral_fin, ← Finset.sum_sdiff (Finset.subset_univ P)]
  rw [Finset.sum_eq_zero (fun t ht => by rw [hzero t ht]; ring)]
  rw [hP, Finset.sum_pair huv]
  ring

lemma integral_step_state {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (h : MDPTrajectory S A n) (g : Fin S → ℝ) :
    (∫ p, g p.1 ∂(mdpStepKernel M μ0 π n h)) = ∫ s, g s ∂(mdpStateKernel M μ0 n h) := by
  rw [mdpStepKernel, ProbabilityTheory.integral_compProd (by exact Integrable.of_finite)]
  simp

lemma integral_state_zero (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 0 h)) = ∫ s, g s ∂μ0.toMeasure := by
  rw [mdpStateKernel]; simp

lemma integral_state_succ {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A (n + 1)) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 (n + 1) h))
      = ∫ s, g s ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply]; rfl

/-- The probability that the state of round `n + 1` has class one. -/
noncomputable def w (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ : Fin S) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π n h))
      ∂(mdpMeasure M (mdpStateDirac s₀) π n)

lemma w_zero (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S) :
    w ρ M π s₀ 0 = ρ s₀ := by
  have hz : ∀ h : MDPTrajectory S A 0,
      (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π 0 h)) = ρ s₀ := by
    intro h
    rw [integral_step_state, integral_state_zero, integral_fin]
    rw [Finset.sum_eq_single s₀]
    · simp [mdpStateDirac]
    · intro b _ hb
      simp [mdpStateDirac, hb]
    · intro hcon
      exact absurd (Finset.mem_univ s₀) hcon
  rw [w]
  simp [hz]

lemma integral_last_state (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ : Fin S) (n : ℕ) :
    (∫ h, ρ (h (Fin.last n)).1 ∂(mdpMeasure M (mdpStateDirac s₀) π (n + 1)))
      = w ρ M π s₀ n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀) π n
    (fun h' => ρ (h' (Fin.last n)).1), w]
  simp

/-- The one-step recursion, given the pointwise row identity. -/
lemma w_succ {δ : ℝ} (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ : Fin S)
    (hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ρ s) (n : ℕ) :
    w ρ M π s₀ (n + 1) = δ + (1 - 2 * δ) * w ρ M π s₀ n := by
  have hinner : ∀ h : MDPTrajectory S A (n + 1),
      (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π (n + 1) h))
        = δ + (1 - 2 * δ) * ρ (h (Fin.last n)).1 := by
    intro h
    rw [integral_step_state, integral_state_succ]
    exact hrow _ _
  rw [w]
  simp_rw [hinner]
  rw [integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_last_state]
  simp

lemma w_eq {δ : ℝ} (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S)
    (hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ρ s) (n : ℕ) :
    w ρ M π s₀ n = 1 / 2 + (ρ s₀ - 1 / 2) * (1 - 2 * δ) ^ n := by
  induction n with
  | zero => rw [w_zero]; simp
  | succ n ih =>
      rw [w_succ ρ M π s₀ hrow n, ih]
      ring

/-- The reward accumulated over `n` rounds. -/
noncomputable def R (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S) (n : ℕ) : ℝ :=
  ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s₀) π n)

lemma reward_snoc (ρ : Fin S → ℝ) (M : FiniteMDP S A) (hr : ∀ s b, M.r s b = ρ s)
    {n : ℕ} (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + ρ p.1 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro t _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last, hr]

lemma R_zero (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S) : R M π s₀ 0 = 0 := by
  rw [R]
  have : ∀ h : MDPTrajectory S A 0, mdpTrajectoryReward M h = 0 := by
    intro h; rw [mdpTrajectoryReward]; simp
  simp [this]

lemma R_succ (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S)
    (hr : ∀ s b, M.r s b = ρ s) (n : ℕ) :
    R M π s₀ (n + 1) = R M π s₀ n + w ρ M π s₀ n := by
  rw [R, BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀) π n
    (fun h' => mdpTrajectoryReward M h')]
  simp_rw [reward_snoc ρ M hr]
  have hin : ∀ h : MDPTrajectory S A n,
      (∫ p, (mdpTrajectoryReward M h + ρ p.1)
          ∂(mdpStepKernel M (mdpStateDirac s₀) π n h))
        = mdpTrajectoryReward M h
            + ∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π n h) := by
    intro h
    rw [integral_add (integrable_const _) (by exact Integrable.of_finite), integral_const]
    simp
  simp_rw [hin]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite), R, w]

lemma R_eq_sum (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ : Fin S)
    (hr : ∀ s b, M.r s b = ρ s) (T : ℕ) :
    R M π s₀ T = ∑ n ∈ Finset.range T, w ρ M π s₀ n := by
  induction T with
  | zero => rw [R_zero]; simp
  | succ T ih => rw [R_succ ρ M π s₀ hr T, ih, Finset.sum_range_succ]

/-- The indicator of the planted pair. -/
def indp (sStar : Fin S) (bStar : Fin A) (p : Fin S × Fin A) : ℝ :=
  if p = (sStar, bStar) then 1 else 0

/-- The probability that round `n + 1` plays the planted pair. -/
noncomputable def q (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ sStar : Fin S)
    (bStar : Fin A) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, indp sStar bStar p ∂(mdpStepKernel M (mdpStateDirac s₀) π n h))
      ∂(mdpMeasure M (mdpStateDirac s₀) π n)

lemma q_nonneg (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ sStar : Fin S)
    (bStar : Fin A) (n : ℕ) : 0 ≤ q M π s₀ sStar bStar n := by
  rw [q]
  refine integral_nonneg fun h => integral_nonneg fun p => ?_
  rw [indp]; positivity

lemma integral_last_indp (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ sStar : Fin S)
    (bStar : Fin A) (n : ℕ) :
    (∫ h, indp sStar bStar (h (Fin.last n))
        ∂(mdpMeasure M (mdpStateDirac s₀) π (n + 1)))
      = q M π s₀ sStar bStar n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀) π n
    (fun h' => indp sStar bStar (h' (Fin.last n))), q]
  simp

/-- The one-step recursion for a planted gadget. -/
lemma w_succ_planted {δ ε : ℝ} (ρ : Fin S → ℝ) (M : FiniteMDP S A) (π : MDPPolicy S A)
    (s₀ sStar : Fin S) (bStar : Fin A)
    (hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M.transitionDist s b).toMeasure)
        = δ + (1 - 2 * δ) * ρ s + ε * indp sStar bStar (s, b)) (n : ℕ) :
    w ρ M π s₀ (n + 1)
      = δ + (1 - 2 * δ) * w ρ M π s₀ n + ε * q M π s₀ sStar bStar n := by
  have hinner : ∀ h : MDPTrajectory S A (n + 1),
      (∫ p, ρ p.1 ∂(mdpStepKernel M (mdpStateDirac s₀) π (n + 1) h))
        = δ + (1 - 2 * δ) * ρ (h (Fin.last n)).1
            + ε * indp sStar bStar (h (Fin.last n)) := by
    intro h
    rw [integral_step_state, integral_state_succ]
    have := hrow (h (Fin.last n)).1 (h (Fin.last n)).2
    simpa using this
  rw [w]
  simp_rw [hinner]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
    integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_const_mul, integral_last_state,
    integral_last_indp]
  simp

lemma visit_snoc (sStar : Fin S) (bStar : Fin A) {n : ℕ} (h : MDPTrajectory S A n)
    (p : Fin S × Fin A) :
    (mdpVisitCount (Fin.snoc h p) (n + 1) sStar bStar : ℝ)
      = (mdpVisitCount h n sStar bStar : ℝ) + indp sStar bStar p := by
  classical
  simp only [mdpVisitCount, Finset.card_filter, indp]
  push_cast
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro t _
    rw [Fin.snoc_castSucc]
    have : ((t.castSucc : Fin (n + 1)) : ℕ) < n + 1 := by
      simp [Fin.castSucc]
    have ht : ((t : ℕ) < n) := t.isLt
    simp [this, ht]
  · rw [Fin.snoc_last]
    simp

lemma visit_eq_sum (M : FiniteMDP S A) (π : MDPPolicy S A) (s₀ sStar : Fin S)
    (bStar : Fin A) (T : ℕ) :
    (∫ h, (mdpVisitCount h T sStar bStar : ℝ)
        ∂(mdpMeasure M (mdpStateDirac s₀) π T))
      = ∑ n ∈ Finset.range T, q M π s₀ sStar bStar n := by
  induction T with
  | zero => simp [mdpVisitCount]
  | succ T ih =>
      rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac s₀) π T
        (fun h' => ((mdpVisitCount h' (T + 1) sStar bStar : ℕ) : ℝ))]
      simp_rw [visit_snoc sStar bStar]
      have hin : ∀ h : MDPTrajectory S A T,
          (∫ p, ((mdpVisitCount h T sStar bStar : ℝ) + indp sStar bStar p)
              ∂(mdpStepKernel M (mdpStateDirac s₀) π T h))
            = (mdpVisitCount h T sStar bStar : ℝ)
                + ∫ p, indp sStar bStar p ∂(mdpStepKernel M (mdpStateDirac s₀) π T h) := by
        intro h
        rw [integral_add (integrable_const _) (by exact Integrable.of_finite),
          integral_const]
        simp
      simp_rw [hin]
      rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
        ih, ← q, Finset.sum_range_succ]

end JaoTwoClassOcc

open JaoTwoClassOcc

theorem solution {S A : ℕ}
    (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (ρ : Fin S → ℝ) (up down : Fin S → Fin S) (nav : Fin S → Fin A → Fin S)
    (hρ01 : ∀ s, ρ s = 0 ∨ ρ s = 1)
    (sStar : Fin S) (bStar : Fin A) (M M₀ : FiniteMDP S A)
    (hstar : ρ sStar = 0)
    (hrM : ∀ s b, M.r s b = ρ s)
    (hrow0M : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M.P s b (up s) : ℝ) = δ + (if (s, b) = (sStar, bStar) then ε else 0) ∧
        (M.P s b (nav s b) : ℝ) = 1 - δ - (if (s, b) = (sStar, bStar) then ε else 0))
    (hrow1M : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M.P s b (down s) : ℝ) = δ ∧ (M.P s b s : ℝ) = 1 - δ)
    (hrM₀ : ∀ s b, M₀.r s b = ρ s)
    (hrow0M₀ : ∀ s b, ρ s = 0 →
        ρ (up s) = 1 ∧ ρ (nav s b) = 0 ∧ up s ≠ nav s b ∧
        (M₀.P s b (up s) : ℝ) = δ ∧
        (M₀.P s b (nav s b) : ℝ) = 1 - δ)
    (hrow1M₀ : ∀ s b, ρ s = 1 →
        ρ (down s) = 0 ∧ down s ≠ s ∧
        (M₀.P s b (down s) : ℝ) = δ ∧ (M₀.P s b s : ℝ) = 1 - δ)
    (T : ℕ) (π : MDPPolicy S A) (s₀ : Fin S) :
    (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s₀) π T))
      ≤ (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac s₀) π T))
        + (ε / (2 * δ))
            * ∫ h, (mdpVisitCount h T sStar bStar : ℝ)
                ∂(mdpMeasure M (mdpStateDirac s₀) π T) := by
  classical
  have hp : ∀ (N : FiniteMDP S A) (s' : Fin S) (b' : Fin A) (t : Fin S),
      (((N.transitionDist s' b').prob t : ℝ)) = ((N.P s' b' t : ℝ)) := fun _ _ _ _ => rfl
  -- the reference row identity
  have hrow₀ : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M₀.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ρ s := by
    intro s b
    rcases hρ01 s with hs | hs
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hrow0M₀ s b hs
      rw [integral_two_point _ (up s) (nav s b) h3 (by rw [hp, hp, h4, h5]; ring)]
      rw [hp, hp, h4, h5, h1, h2, hs]; ring
    · obtain ⟨h1, h2, h3, h4⟩ := hrow1M₀ s b hs
      rw [integral_two_point _ (down s) s h2 (by rw [hp, hp, h3, h4]; ring)]
      rw [hp, hp, h3, h4, h1, hs]; ring
  -- the planted row identity: the boost sits exactly on the planted pair
  have hrowM : ∀ (s : Fin S) (b : Fin A),
      (∫ t, ρ t ∂(M.transitionDist s b).toMeasure)
        = δ + (1 - 2 * δ) * ρ s + ε * indp sStar bStar (s, b) := by
    intro s b
    rcases hρ01 s with hs | hs
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hrow0M s b hs
      rw [integral_two_point _ (up s) (nav s b) h3 (by rw [hp, hp, h4, h5]; ring)]
      rw [hp, hp, h4, h5, h1, h2, hs, indp]
      by_cases hc : (s, b) = (sStar, bStar)
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]; ring
    · obtain ⟨h1, h2, h3, h4⟩ := hrow1M s b hs
      have hne : (s, b) ≠ (sStar, bStar) := by
        intro hc
        have hss : s = sStar := congrArg Prod.fst hc
        rw [hss, hstar] at hs
        norm_num at hs
      rw [integral_two_point _ (down s) s h2 (by rw [hp, hp, h3, h4]; ring)]
      rw [hp, hp, h3, h4, h1, hs, indp, if_neg hne]; ring
  -- the two reward streams, as partial sums of the class-one probabilities
  have hrewM := R_eq_sum ρ M π s₀ hrM T
  have hrewM₀ := R_eq_sum ρ M₀ π s₀ hrM₀ T
  rw [R] at hrewM hrewM₀
  -- the gap obeys a linear recursion with no constant term
  set r : ℝ := 1 - 2 * δ with hrdef
  have hr0 : (0 : ℝ) ≤ r := by rw [hrdef]; linarith
  set d : ℕ → ℝ := fun n => w ρ M π s₀ n - w ρ M₀ π s₀ n with hddef
  have hd0 : d 0 = 0 := by rw [hddef]; simp [w_zero]
  have hdrec : ∀ n, d (n + 1) = r * d n + ε * q M π s₀ sStar bStar n := by
    intro n
    rw [hddef]
    simp only
    rw [w_succ_planted ρ M π s₀ sStar bStar hrowM n, w_succ ρ M₀ π s₀ hrow₀ n, hrdef]
    ring
  have hdnn : ∀ n, 0 ≤ d n := by
    intro n
    induction n with
    | zero => rw [hd0]
    | succ n ih =>
        rw [hdrec n]
        have := q_nonneg M π s₀ sStar bStar n
        nlinarith
  -- telescoping
  have hsum : (∑ n ∈ Finset.range T, d (n + 1))
      = r * (∑ n ∈ Finset.range T, d n)
        + ε * ∑ n ∈ Finset.range T, q M π s₀ sStar bStar n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => hdrec n)
  have hshift : (∑ n ∈ Finset.range T, d (n + 1)) = (∑ n ∈ Finset.range T, d n) + d T := by
    have h1 : (∑ n ∈ Finset.range (T + 1), d n) = (∑ n ∈ Finset.range T, d (n + 1)) + d 0 :=
      Finset.sum_range_succ' d T
    have h2 : (∑ n ∈ Finset.range (T + 1), d n) = (∑ n ∈ Finset.range T, d n) + d T :=
      Finset.sum_range_succ d T
    rw [hd0] at h1
    linarith [h1, h2]
  have hdsum : (2 * δ) * (∑ n ∈ Finset.range T, d n)
      ≤ ε * ∑ n ∈ Finset.range T, q M π s₀ sStar bStar n := by
    have := hdnn T
    rw [hrdef] at hsum
    linarith [hsum, hshift]
  -- assemble
  have hsplit : (∑ n ∈ Finset.range T, d n)
      = (∑ n ∈ Finset.range T, w ρ M π s₀ n) - ∑ n ∈ Finset.range T, w ρ M₀ π s₀ n := by
    rw [hddef, ← Finset.sum_sub_distrib]
  have h2δ : (0 : ℝ) < 2 * δ := by linarith
  have hkey : (∑ n ∈ Finset.range T, d n)
      ≤ (ε * ∑ n ∈ Finset.range T, q M π s₀ sStar bStar n) / (2 * δ) := by
    rw [le_div_iff₀ h2δ]; linarith [hdsum]
  rw [hrewM, hrewM₀, visit_eq_sum M π s₀ sStar bStar T]
  have hdiv : (ε / (2 * δ)) * (∑ n ∈ Finset.range T, q M π s₀ sStar bStar n)
      = (ε * ∑ n ∈ Finset.range T, q M π s₀ sStar bStar n) / (2 * δ) := by ring
  rw [hdiv]
  linarith [hkey, hsplit]
