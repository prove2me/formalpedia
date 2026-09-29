-- Prove2me | solution 1 for BanditAlgorithm.jao_two_state_gadget_reward_le_reference_plus_planted_plays
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:45:06.043707+00:00
-- url     : https://prove2.me/submissions/9fd01a2f-d371-49c8-8923-f7f6ddaf5930

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Algebra.Field.GeomSum
import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoEq34

/-- The indicator of the rewarding state `s_p = 1`. -/
def ind1s : Fin 2 → ℝ := fun s => if s = 1 then 1 else 0

lemma fin2_cases (s : Fin 2) : s = 0 ∨ s = 1 := by
  have hlt := s.isLt
  rcases Nat.eq_zero_or_pos s.val with h | h
  · exact Or.inl (Fin.ext (by simp [h]))
  · exact Or.inr (Fin.ext (by simp; omega))

lemma toMeasure_apply {S : ℕ} (d : MDPStateDistribution S) (A : Set (Fin S)) :
    d.toMeasure A = ∑ i, (d.prob i : ℝ≥0∞) * A.indicator 1 i := by
  rw [MDPStateDistribution.toMeasure, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

lemma toMeasure_real_singleton {S : ℕ} (d : MDPStateDistribution S) (s : Fin S) :
    (d.toMeasure).real {s} = (d.prob s : ℝ) := by
  rw [measureReal_def, toMeasure_apply, Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- Integrating a function of the state alone against the step kernel. -/
lemma integral_step_state {S A n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (h : MDPTrajectory S A n) (g : Fin S → ℝ) :
    (∫ p, g p.1 ∂(mdpStepKernel M μ0 π n h)) = ∫ s, g s ∂(mdpStateKernel M μ0 n h) := by
  rw [mdpStepKernel, ProbabilityTheory.integral_compProd (by exact Integrable.of_finite)]
  simp

lemma integral_state_zero {S A : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 0 h)) = ∫ s, g s ∂μ0.toMeasure := by
  rw [mdpStateKernel]; simp

lemma integral_state_succ {S A n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A (n + 1)) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 (n + 1) h))
      = ∫ s, g s ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply]; rfl

lemma integral_two_point (d : MDPStateDistribution 2) (g : Fin 2 → ℝ) :
    (∫ s, g s ∂d.toMeasure) = (d.prob 0 : ℝ) * g 0 + (d.prob 1 : ℝ) * g 1 := by
  rw [integral_fintype (by exact Integrable.of_finite), Fin.sum_univ_two,
    toMeasure_real_singleton, toMeasure_real_singleton, smul_eq_mul, smul_eq_mul]

variable {m : ℕ}

/-- The probability that the state of round `n + 1` is the rewarding state. -/
noncomputable def w (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π n h))
      ∂(mdpMeasure M (mdpStateDirac 0) π n)

lemma w_zero (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) : w M π 0 = 0 := by
  have hz : ∀ h : MDPTrajectory 2 m 0,
      (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π 0 h)) = 0 := by
    intro h
    rw [integral_step_state, integral_state_zero, integral_two_point]
    simp [ind1s, mdpStateDirac]
  rw [w]
  simp [hz]

/-- The law of the state at the end of a trajectory of length `n + 1` is `w M π n`. -/
lemma integral_last_state (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (n : ℕ) :
    (∫ h, ind1s (h (Fin.last n)).1 ∂(mdpMeasure M (mdpStateDirac 0) π (n + 1))) = w M π n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π n
    (fun h' => ind1s (h' (Fin.last n)).1), w]
  simp

lemma w_succ {δ : ℝ} (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ) (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ) (n : ℕ) :
    w M π (n + 1) = δ + (1 - 2 * δ) * w M π n := by
  have hrow : ∀ (s : Fin 2) (b : Fin m),
      (∫ t, ind1s t ∂(M.transitionDist s b).toMeasure) = δ + (1 - 2 * δ) * ind1s s := by
    intro s b
    rw [integral_two_point]
    have h1 : ∀ (s' : Fin 2) (b' : Fin m), ((M.transitionDist s' b').prob 1 : ℝ) = (M.P s' b' 1 : ℝ) :=
      fun _ _ => rfl
    rcases fin2_cases s with hs | hs
    · subst hs
      rw [h1, hP0 b]
      simp [ind1s]
    · subst hs
      have hsum := M.P_sum_one 1 b
      rw [Fin.sum_univ_two] at hsum
      have : (M.P 1 b 0 : ℝ) + (M.P 1 b 1 : ℝ) = 1 := by
        rw [← NNReal.coe_add, hsum, NNReal.coe_one]
      rw [hP1 b] at this
      rw [h1]
      simp only [ind1s]
      norm_num
      linarith
  have hinner : ∀ h : MDPTrajectory 2 m (n + 1),
      (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π (n + 1) h))
        = δ + (1 - 2 * δ) * ind1s (h (Fin.last n)).1 := by
    intro h
    rw [integral_step_state, integral_state_succ]
    exact hrow _ _
  rw [w]
  simp_rw [hinner]
  rw [integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_last_state]
  simp

lemma w_eq {δ : ℝ} (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ) (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ) (n : ℕ) :
    w M π n = (1 - (1 - 2 * δ) ^ n) / 2 := by
  induction n with
  | zero => rw [w_zero]; simp
  | succ n ih =>
      rw [w_succ M π hP1 hP0 n, ih]
      ring

/-- The reward accumulated over `n` rounds. -/
noncomputable def R (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (n : ℕ) : ℝ :=
  ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac 0) π n)

lemma reward_snoc (M : FiniteMDP 2 m) (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    {n : ℕ} (h : MDPTrajectory 2 m n) (p : Fin 2 × Fin m) :
    mdpTrajectoryReward M (Fin.snoc h p) = mdpTrajectoryReward M h + ind1s p.1 := by
  rw [mdpTrajectoryReward, mdpTrajectoryReward, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro t _
    rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]
    rcases fin2_cases p.1 with hs | hs
    · rw [hs, hr0]; simp [ind1s, hs]
    · rw [hs, hr1]; simp [ind1s, hs]

lemma R_zero (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) : R M π 0 = 0 := by
  rw [R]
  have : ∀ h : MDPTrajectory 2 m 0, mdpTrajectoryReward M h = 0 := by
    intro h; rw [mdpTrajectoryReward]; simp
  simp [this]

lemma R_succ (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1) (n : ℕ) :
    R M π (n + 1) = R M π n + w M π n := by
  rw [R, BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π n
    (fun h' => mdpTrajectoryReward M h')]
  simp_rw [reward_snoc M hr0 hr1]
  have hin : ∀ h : MDPTrajectory 2 m n,
      (∫ p, (mdpTrajectoryReward M h + ind1s p.1)
          ∂(mdpStepKernel M (mdpStateDirac 0) π n h))
        = mdpTrajectoryReward M h
            + ∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π n h) := by
    intro h
    rw [integral_add (integrable_const _) (by exact Integrable.of_finite), integral_const]
    simp
  simp_rw [hin]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite), R, w]

lemma R_eq_sum (M : FiniteMDP 2 m) (π : MDPPolicy 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1) (T : ℕ) :
    R M π T = ∑ n ∈ Finset.range T, w M π n := by
  induction T with
  | zero => rw [R_zero]; simp
  | succ T ih => rw [R_succ M π hr0 hr1 T, ih, Finset.sum_range_succ]

/-- The indicator of "the planted action was played in the reference state". -/
def inda {m : ℕ} (a : Fin m) (p : Fin 2 × Fin m) : ℝ := if p = (0, a) then 1 else 0

/-- The probability that round `n + 1` plays the planted action in state `s_0`. -/
noncomputable def q (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (n : ℕ) : ℝ :=
  ∫ h, (∫ p, inda a p ∂(mdpStepKernel M (mdpStateDirac 0) π n h))
      ∂(mdpMeasure M (mdpStateDirac 0) π n)

lemma q_nonneg (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (n : ℕ) : 0 ≤ q M π a n := by
  rw [q]
  apply integral_nonneg
  intro h
  apply integral_nonneg
  intro p
  rw [inda]
  positivity

lemma integral_last_inda (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (n : ℕ) :
    (∫ h, inda a (h (Fin.last n)) ∂(mdpMeasure M (mdpStateDirac 0) π (n + 1))) = q M π a n := by
  rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π n
    (fun h' => inda a (h' (Fin.last n))), q]
  simp

/-- The state recursion for the planted gadget: the escape probability carries the
extra `ε` exactly on the rounds that play the planted action in `s_0`. -/
lemma w_succ_planted {δ ε : ℝ} (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0)) (n : ℕ) :
    w M π (n + 1) = δ + (1 - 2 * δ) * w M π n + ε * q M π a n := by
  have hrow : ∀ (s : Fin 2) (b : Fin m),
      (∫ t, ind1s t ∂(M.transitionDist s b).toMeasure)
        = δ + (1 - 2 * δ) * ind1s s + ε * inda a (s, b) := by
    intro s b
    rw [integral_two_point]
    have h1 : ∀ (s' : Fin 2) (b' : Fin m),
        ((M.transitionDist s' b').prob 1 : ℝ) = (M.P s' b' 1 : ℝ) := fun _ _ => rfl
    rcases fin2_cases s with hs | hs
    · subst hs
      rw [h1, hP0 b]
      by_cases hb : b = a
      · rw [if_pos hb]
        simp [ind1s, inda, hb]
      · rw [if_neg hb]
        have hne : ((0 : Fin 2), b) ≠ ((0 : Fin 2), a) := by
          intro hcon
          exact hb (congrArg Prod.snd hcon)
        simp [ind1s, inda, hne, hb]
    · subst hs
      have hsum := M.P_sum_one 1 b
      rw [Fin.sum_univ_two] at hsum
      have hs2 : (M.P 1 b 0 : ℝ) + (M.P 1 b 1 : ℝ) = 1 := by
        rw [← NNReal.coe_add, hsum, NNReal.coe_one]
      rw [hP1 b] at hs2
      rw [h1]
      have hne : ((1 : Fin 2), b) ≠ ((0 : Fin 2), a) := by
        intro hcon
        have hone : (1 : Fin 2) = 0 := congrArg Prod.fst hcon
        exact absurd hone (by decide)
      simp only [ind1s, inda, if_neg hne]
      norm_num
      linarith
  have hinner : ∀ h : MDPTrajectory 2 m (n + 1),
      (∫ p, ind1s p.1 ∂(mdpStepKernel M (mdpStateDirac 0) π (n + 1) h))
        = δ + (1 - 2 * δ) * ind1s (h (Fin.last n)).1 + ε * inda a (h (Fin.last n)) := by
    intro h
    rw [integral_step_state, integral_state_succ]
    have := hrow (h (Fin.last n)).1 (h (Fin.last n)).2
    rw [this]
  rw [w]
  simp_rw [hinner]
  rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
    integral_add (integrable_const _) (by exact Integrable.of_finite)]
  rw [integral_const, integral_const_mul, integral_const_mul, integral_last_state,
    integral_last_inda]
  simp

/-- Visit counts of the planted action in `s_0`, accumulated. -/
lemma visit_snoc (a : Fin m) {n : ℕ} (h : MDPTrajectory 2 m n) (p : Fin 2 × Fin m) :
    ((mdpVisitCount (Fin.snoc h p) (n + 1) (0 : Fin 2) a : ℕ) : ℝ)
      = ((mdpVisitCount h n (0 : Fin 2) a : ℕ) : ℝ) + inda a p := by
  simp only [mdpVisitCount, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  push_cast
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i _
    rw [Fin.snoc_castSucc]
    have h1 : ((i.castSucc : Fin (n + 1)) : ℕ) < n + 1 := by
      have := i.isLt
      simp only [Fin.val_castSucc]
      omega
    have h2 : ((i : Fin n) : ℕ) < n := i.isLt
    simp [h1, h2]
  · rw [Fin.snoc_last, inda]
    have h1 : ((Fin.last n : Fin (n + 1)) : ℕ) < n + 1 := by simp
    simp [h1]

lemma visit_eq_sum (M : FiniteMDP 2 m) (π : MDPPolicy 2 m) (a : Fin m) (T : ℕ) :
    (∫ h, (mdpVisitCount h T (0 : Fin 2) a : ℝ) ∂(mdpMeasure M (mdpStateDirac 0) π T))
      = ∑ n ∈ Finset.range T, q M π a n := by
  induction T with
  | zero =>
      have : ∀ h : MDPTrajectory 2 m 0, ((mdpVisitCount h 0 (0 : Fin 2) a : ℕ) : ℝ) = 0 := by
        intro h
        simp [mdpVisitCount]
      simp [this]
  | succ T ih =>
      rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac 0) π T
        (fun h' => ((mdpVisitCount h' (T + 1) (0 : Fin 2) a : ℕ) : ℝ))]
      simp_rw [visit_snoc a]
      have hin : ∀ h : MDPTrajectory 2 m T,
          (∫ p, (((mdpVisitCount h T (0 : Fin 2) a : ℕ) : ℝ) + inda a p)
              ∂(mdpStepKernel M (mdpStateDirac 0) π T h))
            = ((mdpVisitCount h T (0 : Fin 2) a : ℕ) : ℝ)
                + ∫ p, inda a p ∂(mdpStepKernel M (mdpStateDirac 0) π T h) := by
        intro h
        rw [integral_add (integrable_const _) (by exact Integrable.of_finite), integral_const]
        simp
      simp_rw [hin]
      rw [integral_add (by exact Integrable.of_finite) (by exact Integrable.of_finite),
        ih, ← q, Finset.sum_range_succ]

end JaoEq34

open JaoEq34

theorem solution
    {m : ℕ} (δ ε : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3) (hε0 : 0 < ε) (hεδ : ε ≤ δ)
    (a : Fin m) (M M₀ : FiniteMDP 2 m)
    (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    (hP1 : ∀ b, (M.P 1 b 0 : ℝ) = δ)
    (hP0 : ∀ b, (M.P 0 b 1 : ℝ) = δ + (if b = a then ε else 0))
    (hr0' : ∀ b, M₀.r 0 b = 0) (hr1' : ∀ b, M₀.r 1 b = 1)
    (hP1' : ∀ b, (M₀.P 1 b 0 : ℝ) = δ) (hP0' : ∀ b, (M₀.P 0 b 1 : ℝ) = δ)
    (T : ℕ) (π : MDPPolicy 2 m) :
    (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac 0) π T))
      ≤ (T : ℝ)
          - (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
          + (ε / δ)
              * ∫ h, (mdpVisitCount h T 0 a : ℝ) ∂(mdpMeasure M (mdpStateDirac 0) π T) := by
  set r : ℝ := 1 - 2 * δ with hrdef
  have hr0'' : (0:ℝ) ≤ r := by rw [hrdef]; linarith
  have hr1'' : r < 1 := by rw [hrdef]; linarith
  -- the deviation of the planted state law from the reference one
  set d : ℕ → ℝ := fun n => w M π n - (1 - r ^ n) / 2 with hddef
  have hd0 : d 0 = 0 := by rw [hddef]; simp [w_zero]
  have hdrec : ∀ n, d (n + 1) = r * d n + ε * q M π a n := by
    intro n
    rw [hddef]
    simp only
    rw [w_succ_planted M π a hP1 hP0 n, hrdef]
    ring
  have hdnn : ∀ n, 0 ≤ d n := by
    intro n
    induction n with
    | zero => rw [hd0]
    | succ n ih =>
        rw [hdrec n]
        have := q_nonneg M π a n
        nlinarith
  -- telescoping: (1 - r) * Σ d = ε * Σ q - d T ≤ ε * Σ q
  have hsum : (∑ n ∈ Finset.range T, d (n + 1))
      = r * (∑ n ∈ Finset.range T, d n) + ε * ∑ n ∈ Finset.range T, q M π a n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => hdrec n)
  have hshift : (∑ n ∈ Finset.range T, d (n + 1)) = (∑ n ∈ Finset.range T, d n) + d T := by
    have h1 : (∑ n ∈ Finset.range (T + 1), d n) = (∑ n ∈ Finset.range T, d (n + 1)) + d 0 :=
      Finset.sum_range_succ' d T
    have h2 : (∑ n ∈ Finset.range (T + 1), d n) = (∑ n ∈ Finset.range T, d n) + d T :=
      Finset.sum_range_succ d T
    rw [hd0] at h1
    linarith [h1, h2]
  have hdsum : (2 * δ) * (∑ n ∈ Finset.range T, d n) ≤ ε * ∑ n ∈ Finset.range T, q M π a n := by
    have := hdnn T
    rw [hshift] at hsum
    rw [hrdef] at hsum
    linarith
  -- the two rewards, as sums of the state probabilities
  have hRM : (∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac 0) π T))
      = ∑ n ∈ Finset.range T, w M π n := R_eq_sum M π hr0 hr1 T
  have hRM0 : (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
      = ∑ n ∈ Finset.range T, (1 - r ^ n) / 2 := by
    have hR0 : R M₀ π T = ∑ n ∈ Finset.range T, w M₀ π n := R_eq_sum M₀ π hr0' hr1' T
    have hgoal : (∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
        = ∑ n ∈ Finset.range T, w M₀ π n := hR0
    rw [hgoal]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [w_eq M₀ π hP1' hP0' n, ← hrdef]
  have hsplit : (∑ n ∈ Finset.range T, w M π n)
      = (∑ n ∈ Finset.range T, (1 - r ^ n) / 2) + ∑ n ∈ Finset.range T, d n := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by rw [hddef]; ring)
  -- the reference reward is at most half the horizon
  have href_le : (∑ n ∈ Finset.range T, (1 - r ^ n) / 2) ≤ (T : ℝ) / 2 := by
    have : ∀ n ∈ Finset.range T, (1 - r ^ n) / 2 ≤ (1:ℝ) / 2 := by
      intro n _
      have : (0:ℝ) ≤ r ^ n := pow_nonneg hr0'' n
      linarith
    calc (∑ n ∈ Finset.range T, (1 - r ^ n) / 2)
        ≤ ∑ _n ∈ Finset.range T, (1:ℝ) / 2 := Finset.sum_le_sum this
      _ = (T : ℝ) / 2 := by simp; ring
  -- the visit counts
  have hvis : (∫ h, (mdpVisitCount h T (0 : Fin 2) a : ℝ) ∂(mdpMeasure M (mdpStateDirac 0) π T))
      = ∑ n ∈ Finset.range T, q M π a n := visit_eq_sum M π a T
  have hqnn : 0 ≤ ∑ n ∈ Finset.range T, q M π a n :=
    Finset.sum_nonneg (fun n _ => q_nonneg M π a n)
  -- assemble
  rw [hRM, hRM0, hsplit, hvis]
  have hkey : (∑ n ∈ Finset.range T, d n) ≤ (ε / (2 * δ)) * ∑ n ∈ Finset.range T, q M π a n := by
    have h2δ : (0:ℝ) < 2 * δ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ h2δ]
    linarith [hdsum]
  have hfrac : (ε / (2 * δ)) * (∑ n ∈ Finset.range T, q M π a n)
      ≤ (ε / δ) * ∑ n ∈ Finset.range T, q M π a n := by
    apply mul_le_mul_of_nonneg_right _ hqnn
    rw [div_le_div_iff₀ (by linarith) hδ0]
    nlinarith
  linarith [href_le, hkey, hfrac]
