-- Prove2me | solution 1 for BanditAlgorithm.mdp_travel_time_le_of_lyapunov_drift
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T04:12:42.41192+00:00
-- url     : https://prove2.me/submissions/39a9bdec-18a3-4b44-83f9-323659a99071

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Definitions.Def_FiniteMDPLearning
import Theorems.Thm_BanditAlgorithm_mdp_integral_trajectory_succ

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal NNReal BigOperators

namespace MDPDrift

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

lemma integral_dirac_dist (src : Fin S) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateDirac src).toMeasure) = g src := by
  rw [integral_fin, Finset.sum_eq_single src]
  · simp [mdpStateDirac]
  · intro b _ hb
    simp [mdpStateDirac, hb]
  · intro hc
    exact absurd (Finset.mem_univ src) hc

lemma integral_state_zero (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A 0) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 0 h)) = ∫ s, g s ∂μ0.toMeasure := by
  rw [mdpStateKernel]; simp

lemma integral_state_succ {n : ℕ} (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (h : MDPTrajectory S A (n + 1)) (g : Fin S → ℝ) :
    (∫ s, g s ∂(mdpStateKernel M μ0 (n + 1) h))
      = ∫ s, g s ∂(M.transitionDist (h (Fin.last n)).1 (h (Fin.last n)).2).toMeasure := by
  rw [mdpStateKernel, Kernel.comap_apply]; rfl

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

open Classical in
/-- The indicator that the target has not been visited. -/
noncomputable def sSurv (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) : ℝ :=
  if ∀ t, (h t).1 ≠ tgt then 1 else 0

open Classical in
/-- The indicator that every recorded action is the one `f` prescribes. -/
noncomputable def sAct (f : Fin S → Fin A) {n : ℕ} (h : MDPTrajectory S A n) : ℝ :=
  if ∀ t, (h t).2 = f (h t).1 then 1 else 0

lemma snoc_all_state (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    (∀ t, ((Fin.snoc h p : MDPTrajectory S A (n + 1)) t).1 ≠ tgt)
      ↔ (∀ t, (h t).1 ≠ tgt) ∧ p.1 ≠ tgt := by
  constructor
  · intro hall
    refine ⟨fun t ↦ ?_, ?_⟩
    · have := hall (Fin.castSucc t); rwa [Fin.snoc_castSucc] at this
    · have := hall (Fin.last n); rwa [Fin.snoc_last] at this
  · rintro ⟨h1, h2⟩ t
    refine Fin.lastCases ?_ ?_ t
    · rwa [Fin.snoc_last]
    · intro i; rw [Fin.snoc_castSucc]; exact h1 i

lemma snoc_all_act (f : Fin S → Fin A) {n : ℕ} (h : MDPTrajectory S A n)
    (p : Fin S × Fin A) :
    (∀ t, ((Fin.snoc h p : MDPTrajectory S A (n + 1)) t).2
        = f ((Fin.snoc h p : MDPTrajectory S A (n + 1)) t).1)
      ↔ (∀ t, (h t).2 = f (h t).1) ∧ p.2 = f p.1 := by
  constructor
  · intro hall
    refine ⟨fun t ↦ ?_, ?_⟩
    · have := hall (Fin.castSucc t); rwa [Fin.snoc_castSucc] at this
    · have := hall (Fin.last n); rwa [Fin.snoc_last] at this
  · rintro ⟨h1, h2⟩ t
    refine Fin.lastCases ?_ ?_ t
    · rwa [Fin.snoc_last]
    · intro i; rw [Fin.snoc_castSucc]; exact h1 i

lemma sSurv_snoc (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) (p : Fin S × Fin A) :
    sSurv tgt (Fin.snoc h p : MDPTrajectory S A (n + 1))
      = sSurv tgt h * (if p.1 ≠ tgt then (1 : ℝ) else 0) := by
  classical
  simp only [sSurv, snoc_all_state]
  by_cases h1 : ∀ t, (h t).1 ≠ tgt <;> by_cases h2 : p.1 ≠ tgt <;> simp [h1, h2]

lemma sAct_snoc (f : Fin S → Fin A) {n : ℕ} (h : MDPTrajectory S A n)
    (p : Fin S × Fin A) :
    sAct f (Fin.snoc h p : MDPTrajectory S A (n + 1))
      = sAct f h * (if p.2 = f p.1 then (1 : ℝ) else 0) := by
  classical
  simp only [sAct, snoc_all_act]
  by_cases h1 : ∀ t, (h t).2 = f (h t).1 <;> by_cases h2 : p.2 = f p.1 <;> simp [h1, h2]

lemma sSurv_zero_traj (tgt : Fin S) (h : MDPTrajectory S A 0) : sSurv tgt h = 1 := by
  classical
  rw [sSurv, if_pos]
  intro t
  exact t.elim0

lemma sAct_zero_traj (f : Fin S → Fin A) (h : MDPTrajectory S A 0) : sAct f h = 1 := by
  classical
  rw [sAct, if_pos]
  intro t
  exact t.elim0

lemma sSurv_nonneg (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) : 0 ≤ sSurv tgt h := by
  classical
  rw [sSurv]; split_ifs <;> norm_num

lemma sSurv_le_one (tgt : Fin S) {n : ℕ} (h : MDPTrajectory S A n) : sSurv tgt h ≤ 1 := by
  classical
  rw [sSurv]; split_ifs <;> norm_num

lemma sAct_nonneg (f : Fin S → Fin A) {n : ℕ} (h : MDPTrajectory S A n) : 0 ≤ sAct f h := by
  classical
  rw [sAct]; split_ifs <;> norm_num

lemma sAct_le_one (f : Fin S → Fin A) {n : ℕ} (h : MDPTrajectory S A n) : sAct f h ≤ 1 := by
  classical
  rw [sAct]; split_ifs <;> norm_num

/-- Under the memoryless deterministic policy `f` every recorded action is
`f` of the recorded state, almost surely. -/
lemma integral_sAct (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (f : Fin S → Fin A) (n : ℕ) :
    (∫ h, sAct f h ∂(mdpMeasure M μ0 (mdpMemorylessDetPolicy f) n)) = 1 := by
  induction n with
  | zero =>
      have hz : ∀ h : MDPTrajectory S A 0, sAct f h = 1 := sAct_zero_traj f
      simp_rw [hz]
      simp
  | succ n ih =>
      rw [BanditAlgorithm.mdp_integral_trajectory_succ M μ0 (mdpMemorylessDetPolicy f) n
        (fun h' ↦ sAct f h')]
      have hin : ∀ h : MDPTrajectory S A n,
          (∫ p, sAct f (Fin.snoc h p)
              ∂(mdpStepKernel M μ0 (mdpMemorylessDetPolicy f) n h)) = sAct f h := by
        intro h
        simp_rw [sAct_snoc]
        rw [integral_const_mul, integral_step_det]
        simp
      simp_rw [hin]
      exact ih

end MDPDrift

open MDPDrift

theorem solution {S A : ℕ} (M : FiniteMDP S A)
    (f : Fin S → Fin A) (src tgt : Fin S) (V : Fin S → ℝ)
    (hV0 : ∀ s, 0 ≤ V s)
    (hdrift : ∀ s, s ≠ tgt → (∑ s', (M.P s (f s) s' : ℝ) * V s') + 1 ≤ V s) :
    mdpTravelTime M f src tgt ≤ ENNReal.ofReal (V src) := by
  classical
  set w : ℕ → ℝ := fun k ↦ ∫ h, sSurv tgt h * sAct f h
    ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) with hwdef
  set u : ℕ → ℝ := fun k ↦ ∫ h, sSurv tgt h * sAct f h * V (h (Fin.last k)).1
    ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) with hudef
  have hw0 : ∀ k, 0 ≤ w k := by
    intro k
    rw [hwdef]
    exact integral_nonneg fun h ↦ mul_nonneg (sSurv_nonneg _ _) (sAct_nonneg _ _)
  have hu0 : ∀ k, 0 ≤ u k := by
    intro k
    rw [hudef]
    exact integral_nonneg fun h ↦
      mul_nonneg (mul_nonneg (sSurv_nonneg _ _) (sAct_nonneg _ _)) (hV0 _)
  -- the one-step integral of the truncated Lyapunov function, along a row
  have hrow : ∀ (s : Fin S) (b : Fin A),
      (∫ t, (if t ≠ tgt then (1 : ℝ) else 0) * V t ∂(M.transitionDist s b).toMeasure)
        ≤ ∑ s', (M.P s b s' : ℝ) * V s' := by
    intro s b
    rw [integral_fin]
    refine Finset.sum_le_sum ?_
    intro t _
    have hpb : ((M.transitionDist s b).prob t : ℝ) = (M.P s b t : ℝ) := rfl
    rw [hpb]
    by_cases ht : t ≠ tgt
    · rw [if_pos ht, one_mul]
    · rw [if_neg ht, zero_mul, mul_zero]
      exact mul_nonneg (M.P s b t).coe_nonneg (hV0 t)
  -- the base value
  have hubase : u 0 ≤ V src := by
    rw [hudef]
    simp only
    rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac src)
      (mdpMemorylessDetPolicy f) 0
      (fun h' ↦ sSurv tgt h' * sAct f h' * V (h' (Fin.last 0)).1)]
    have hin : ∀ h : MDPTrajectory S A 0,
        (∫ p, sSurv tgt (Fin.snoc h p) * sAct f (Fin.snoc h p)
              * V ((Fin.snoc h p : MDPTrajectory S A 1) (Fin.last 0)).1
            ∂(mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) 0 h))
          ≤ V src := by
      intro h
      have hpt : ∀ p : Fin S × Fin A,
          sSurv tgt (Fin.snoc h p) * sAct f (Fin.snoc h p)
              * V ((Fin.snoc h p : MDPTrajectory S A 1) (Fin.last 0)).1
            = (if p.1 ≠ tgt then (1 : ℝ) else 0) * (if p.2 = f p.1 then (1 : ℝ) else 0)
                * V p.1 := by
        intro p
        rw [sSurv_snoc, sAct_snoc, sSurv_zero_traj, sAct_zero_traj, Fin.snoc_last]
        ring
      simp_rw [hpt]
      rw [integral_step_det, integral_state_zero]
      rw [integral_dirac_dist]
      split_ifs <;> linarith [hV0 src]
    calc (∫ h, (∫ p, sSurv tgt (Fin.snoc h p) * sAct f (Fin.snoc h p)
            * V ((Fin.snoc h p : MDPTrajectory S A 1) (Fin.last 0)).1
          ∂(mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) 0 h))
        ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) 0))
        ≤ ∫ _h, V src ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) 0) :=
          integral_mono (by exact Integrable.of_finite) (by exact Integrable.of_finite) hin
      _ = V src := by simp
  -- the drift step
  have hstep : ∀ k, u (k + 1) + w k ≤ u k := by
    intro k
    have hexp : u (k + 1)
        = ∫ h, sSurv tgt h * sAct f h *
            (∫ p, (if p.1 ≠ tgt then (1 : ℝ) else 0) * (if p.2 = f p.1 then (1 : ℝ) else 0)
                * V p.1
              ∂(mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1) h))
          ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) := by
      rw [hudef]
      simp only
      rw [BanditAlgorithm.mdp_integral_trajectory_succ M (mdpStateDirac src)
        (mdpMemorylessDetPolicy f) (k + 1)
        (fun h' ↦ sSurv tgt h' * sAct f h' * V (h' (Fin.last (k + 1))).1)]
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro h
      have hpt : ∀ p : Fin S × Fin A,
          sSurv tgt (Fin.snoc h p) * sAct f (Fin.snoc h p)
              * V ((Fin.snoc h p : MDPTrajectory S A (k + 2)) (Fin.last (k + 1))).1
            = sSurv tgt h * sAct f h *
                ((if p.1 ≠ tgt then (1 : ℝ) else 0) * (if p.2 = f p.1 then (1 : ℝ) else 0)
                  * V p.1) := by
        intro p
        rw [sSurv_snoc, sAct_snoc, Fin.snoc_last]
        ring
      simp_rw [hpt]
      rw [integral_const_mul]
    have hbnd : ∀ h : MDPTrajectory S A (k + 1),
        sSurv tgt h * sAct f h *
            (∫ p, (if p.1 ≠ tgt then (1 : ℝ) else 0) * (if p.2 = f p.1 then (1 : ℝ) else 0)
                * V p.1
              ∂(mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1) h))
          ≤ sSurv tgt h * sAct f h * V (h (Fin.last k)).1 - sSurv tgt h * sAct f h := by
      intro h
      by_cases hs : ∀ t, (h t).1 ≠ tgt
      · by_cases ha : ∀ t, (h t).2 = f (h t).1
        · have h1 : sSurv tgt h = 1 := by rw [sSurv, if_pos hs]
          have h2 : sAct f h = 1 := by rw [sAct, if_pos ha]
          rw [h1, h2]
          simp only [one_mul]
          have hlast : (h (Fin.last k)).2 = f (h (Fin.last k)).1 := ha (Fin.last k)
          have hne : (h (Fin.last k)).1 ≠ tgt := hs (Fin.last k)
          have hinner : (∫ p, (if p.1 ≠ tgt then (1 : ℝ) else 0)
                * (if p.2 = f p.1 then (1 : ℝ) else 0) * V p.1
              ∂(mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1) h))
              = ∫ t, (if t ≠ tgt then (1 : ℝ) else 0) * V t
                  ∂(M.transitionDist (h (Fin.last k)).1 (f (h (Fin.last k)).1)).toMeasure := by
            rw [integral_step_det, integral_state_succ, hlast]
            simp
          rw [hinner]
          have hr := hrow (h (Fin.last k)).1 (f (h (Fin.last k)).1)
          have hd := hdrift (h (Fin.last k)).1 hne
          linarith
        · have h2 : sAct f h = 0 := by rw [sAct, if_neg ha]
          rw [h2]
          simp
      · have h1 : sSurv tgt h = 0 := by rw [sSurv, if_neg hs]
        rw [h1]
        simp
    have hmono : (∫ h, sSurv tgt h * sAct f h *
          (∫ p, (if p.1 ≠ tgt then (1 : ℝ) else 0) * (if p.2 = f p.1 then (1 : ℝ) else 0)
              * V p.1
            ∂(mdpStepKernel M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1) h))
          ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)))
        ≤ ∫ h, (sSurv tgt h * sAct f h * V (h (Fin.last k)).1 - sSurv tgt h * sAct f h)
            ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) :=
      integral_mono (by exact Integrable.of_finite) (by exact Integrable.of_finite) hbnd
    rw [integral_sub (by exact Integrable.of_finite) (by exact Integrable.of_finite)] at hmono
    have hUk : u k = ∫ h, sSurv tgt h * sAct f h * V (h (Fin.last k)).1
        ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) := by
      simp only [hudef]
    have hWk : w k = ∫ h, sSurv tgt h * sAct f h
        ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) := by
      simp only [hwdef]
    rw [hexp, hUk, hWk]
    linarith
  -- telescoping
  have haux : ∀ N, (∑ k ∈ Finset.range N, w k) + u N ≤ u 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ]
        linarith [hstep N]
  have hpartial : ∀ N, ∑ k ∈ Finset.range N, w k ≤ V src := by
    intro N
    linarith [haux N, hu0 N, hubase]
  -- the survival probability is `w`, the action constraint holding almost surely
  have hmeasSet : ∀ k : ℕ,
      MeasurableSet {h : MDPTrajectory S A (k + 1) | ∀ t, (h t).1 ≠ tgt} :=
    fun k ↦ (Set.toFinite _).measurableSet
  have hind : ∀ (k : ℕ) (h : MDPTrajectory S A (k + 1)),
      Set.indicator {h : MDPTrajectory S A (k + 1) | ∀ t, (h t).1 ≠ tgt}
          (1 : MDPTrajectory S A (k + 1) → ℝ) h
        = sSurv tgt h := by
    intro k h
    rw [sSurv]
    by_cases hh : ∀ t, (h t).1 ≠ tgt
    · rw [if_pos hh]
      exact Set.indicator_of_mem
        (show h ∈ {h : MDPTrajectory S A (k + 1) | ∀ t, (h t).1 ≠ tgt} from hh) 1
    · rw [if_neg hh]
      exact Set.indicator_of_notMem
        (show h ∉ {h : MDPTrajectory S A (k + 1) | ∀ t, (h t).1 ≠ tgt} from hh) 1
  have hqw : ∀ k, (∫ h, sSurv tgt h
      ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1))) = w k := by
    intro k
    have hsplit : ∀ h : MDPTrajectory S A (k + 1),
        sSurv tgt h * (1 - sAct f h) = sSurv tgt h - sSurv tgt h * sAct f h :=
      fun h ↦ by ring
    have h2 : (0 : ℝ) ≤ ∫ h, sSurv tgt h * (1 - sAct f h)
        ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) :=
      integral_nonneg fun h ↦
        mul_nonneg (sSurv_nonneg _ _) (by linarith [sAct_le_one f h])
    have h1 : (∫ h, sSurv tgt h * (1 - sAct f h)
        ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1))) ≤ 0 := by
      have hle : ∀ h : MDPTrajectory S A (k + 1),
          sSurv tgt h * (1 - sAct f h) ≤ 1 - sAct f h := by
        intro h
        nlinarith [sSurv_le_one tgt h, sSurv_nonneg tgt h, sAct_le_one f h, sAct_nonneg f h]
      calc (∫ h, sSurv tgt h * (1 - sAct f h)
            ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)))
          ≤ ∫ h, (1 - sAct f h)
              ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) :=
            integral_mono (by exact Integrable.of_finite) (by exact Integrable.of_finite) hle
        _ = 0 := by
            rw [integral_sub (integrable_const _) (by exact Integrable.of_finite),
              integral_const, integral_sAct]
            simp
    have h3 : (∫ h, sSurv tgt h * (1 - sAct f h)
          ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)))
        = (∫ h, sSurv tgt h
            ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)))
          - ∫ h, sSurv tgt h * sAct f h
              ∂(mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)) := by
      simp_rw [hsplit]
      rw [integral_sub (by exact Integrable.of_finite) (by exact Integrable.of_finite)]
    rw [hwdef]
    simp only
    linarith
  have hterm : ∀ k : ℕ,
      mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)
          {h | ∀ t, (h t).1 ≠ tgt}
        = ENNReal.ofReal (w k) := by
    intro k
    have hreal : (mdpMeasure M (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)).real
        {h | ∀ t, (h t).1 ≠ tgt} = w k := by
      rw [← integral_indicator_one (hmeasSet k), ← hqw k]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun h ↦ hind k h))
    rw [← hreal, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [mdpTravelTime]
  simp_rw [hterm]
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le ?_
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw0 i)]
  exact ENNReal.ofReal_le_ofReal (hpartial N)
