-- Prove2me | solution 1 for BanditAlgorithm.jao_two_state_reference_occupancy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-05T18:40:20.311857+00:00
-- url     : https://prove2.me/submissions/d703bf59-bf1e-4bc1-8f02-bce4ef8434b3

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Algebra.Field.GeomSum
import Definitions.Def_UCRL2ConfidenceSets
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace JaoOcc

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

/-- The pointwise counting identity: rounds spent in `s_p` plus rounds spent in
`s_∘` (summed over the action played there) is the horizon. -/
lemma count_identity (M : FiniteMDP 2 m) (hr0 : ∀ b, M.r 0 b = 0) (hr1 : ∀ b, M.r 1 b = 1)
    {T : ℕ} (h : MDPTrajectory 2 m T) :
    mdpTrajectoryReward M h + ∑ b : Fin m, (mdpVisitCount h T 0 b : ℝ) = T := by
  have hrew : mdpTrajectoryReward M h = ∑ t : Fin T, ind1s (h t).1 := by
    rw [mdpTrajectoryReward]
    refine Finset.sum_congr rfl ?_
    intro t _
    rcases fin2_cases (h t).1 with hs | hs
    · rw [hs, hr0]; simp [ind1s, hs]
    · rw [hs, hr1]; simp [ind1s, hs]
  have hcount : (∑ b : Fin m, mdpVisitCount h T 0 b)
      = (Finset.univ.filter fun i : Fin T => (h i).1 = 0).card := by
    simp only [mdpVisitCount, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hi : (i : ℕ) < T := i.isLt
    by_cases hz : (h i).1 = 0
    · rw [if_pos hz, Finset.sum_eq_single (h i).2]
      · rw [if_pos ⟨hi, by rw [Prod.ext_iff]; exact ⟨hz, rfl⟩⟩]
      · intro b _ hb
        refine if_neg ?_
        rintro ⟨-, he⟩
        rw [Prod.ext_iff] at he
        exact hb he.2.symm
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    · rw [if_neg hz, Finset.sum_eq_zero]
      intro b _
      refine if_neg ?_
      rintro ⟨-, he⟩
      rw [Prod.ext_iff] at he
      exact hz he.1
  have hcast : ∑ b : Fin m, (mdpVisitCount h T 0 b : ℝ)
      = ((Finset.univ.filter fun i : Fin T => (h i).1 = 0).card : ℝ) := by
    rw [← hcount]
    push_cast
    rfl
  rw [hrew, hcast, Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (g := fun _ : Fin T => (1:ℝ)) ?_]
  · simp
  · intro t _
    rcases fin2_cases (h t).1 with hs | hs
    · simp [ind1s, hs]
    · simp [ind1s, hs]

end JaoOcc

open JaoOcc

theorem solution
    {m : ℕ} (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (M₀ : FiniteMDP 2 m)
    (hr0 : ∀ b, M₀.r 0 b = 0) (hr1 : ∀ b, M₀.r 1 b = 1)
    (hP1 : ∀ b, (M₀.P 1 b 0 : ℝ) = δ) (hP0 : ∀ b, (M₀.P 0 b 1 : ℝ) = δ)
    (T : ℕ) (π : MDPPolicy 2 m) :
    (T : ℝ) / 2 - 1 / (2 * δ)
        ≤ ∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T)
      ∧ ∑ b : Fin m,
            (∫ h, (mdpVisitCount h T 0 b : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac 0) π T))
          ≤ (T : ℝ) / 2 + 1 / (2 * δ) := by
  set r : ℝ := 1 - 2 * δ with hr
  have hr0' : (0:ℝ) ≤ r := by rw [hr]; linarith
  have hr1' : r < 1 := by rw [hr]; linarith
  -- the geometric sum
  have hgeom : ∑ n ∈ Finset.range T, r ^ n ≤ 1 / (2 * δ) := by
    have hne : r ≠ 1 := ne_of_lt hr1'
    have h1r : (0:ℝ) < 1 - r := by linarith
    have hstep : ∑ n ∈ Finset.range T, r ^ n = (1 - r ^ T) / (1 - r) := by
      rw [geom_sum_eq hne]
      field_simp
      ring
    have hEq : (1:ℝ) - r = 2 * δ := by rw [hr]; ring
    have hrT : (0:ℝ) ≤ r ^ T := pow_nonneg hr0' T
    rw [hstep, hEq]
    apply div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- the reward bound
  have hR : R M₀ π T = (T : ℝ) / 2 - (∑ n ∈ Finset.range T, r ^ n) / 2 := by
    rw [R_eq_sum M₀ π hr0 hr1]
    rw [Finset.sum_congr rfl (fun n _ => w_eq M₀ π hP1 hP0 n)]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
    ring
  have hposd : (0:ℝ) < 1 / (2 * δ) := by positivity
  constructor
  · have hid : R M₀ π T
        = ∫ h, mdpTrajectoryReward M₀ h ∂(mdpMeasure M₀ (mdpStateDirac 0) π T) := rfl
    rw [← hid, hR]
    linarith
  · have hsum : (∑ b : Fin m,
        (∫ h, (mdpVisitCount h T 0 b : ℝ) ∂(mdpMeasure M₀ (mdpStateDirac 0) π T)))
      = (T : ℝ) - R M₀ π T := by
      rw [← integral_finset_sum _ (fun b _ => (by exact Integrable.of_finite))]
      have hpt : ∀ h : MDPTrajectory 2 m T, (∑ b : Fin m, (mdpVisitCount h T 0 b : ℝ))
          = (T : ℝ) - mdpTrajectoryReward M₀ h := by
        intro h
        have := count_identity M₀ hr0 hr1 (T := T) h
        linarith
      simp_rw [hpt]
      rw [integral_sub (integrable_const _) (by exact Integrable.of_finite), integral_const, R]
      simp
    rw [hsum, hR]
    linarith
