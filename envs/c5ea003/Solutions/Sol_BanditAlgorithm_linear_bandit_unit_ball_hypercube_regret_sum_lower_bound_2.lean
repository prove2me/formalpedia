-- Prove2me | solution 2 for BanditAlgorithm.linear_bandit_unit_ball_hypercube_regret_sum_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T18:28:25.809362+00:00
-- url     : https://prove2.me/submissions/db02e6cb-65b3-4715-8277-6b04585dc652
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_stopped_loss_change_of_measure
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open Matrix

namespace BanditAlgorithm

attribute [local instance] Classical.propDecidable

private def signOf {d : ℕ} (σ : Fin d → Bool) (i : Fin d) : ℝ :=
  if σ i then 1 else -1

private theorem signOf_sq {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    signOf σ i ^ 2 = 1 := by
  simp [signOf]

private theorem signOf_flip {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    signOf (Function.update σ i (!(σ i))) i = -signOf σ i := by
  cases h : σ i <;> simp [signOf, Function.update, h]

private noncomputable def deltaXI (d n : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) / (48 * n))

private noncomputable def thetaXI {d : ℕ} (n : ℕ)
    (σ : Fin d → Bool) : Fin d → ℝ :=
  fun i ↦ deltaXI d n * signOf σ i

private def activeXI {d n : ℕ} (i : Fin d)
    (h : LinearBanditHistory d n) (t : Fin n) : Prop :=
  (∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s < t),
      ((h s).1 i) ^ 2) < (n : ℝ) / d

private noncomputable def lossXI {d n : ℕ} (i : Fin d)
    (h : LinearBanditHistory d n) (x : ℝ) : ℝ :=
  ∑ t, if activeXI i h t then
    (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0

private theorem dot_sign_le_sqrt {d : ℕ} (hd : 0 < d)
    (a : Fin d → ℝ) (ha : a ⬝ᵥ a ≤ 1) (σ : Fin d → Bool) :
    a ⬝ᵥ signOf σ ≤ Real.sqrt d := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a (signOf σ)
  have hasa : (∑ i : Fin d, a i ^ 2) = a ⬝ᵥ a := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hsig : (∑ i : Fin d, signOf σ i ^ 2) = d := by
    simp [signOf_sq]
  rw [hasa, hsig] at hcs
  have hsqrta : Real.sqrt (a ⬝ᵥ a) ≤ 1 := by
    calc
      Real.sqrt (a ⬝ᵥ a) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt ha
      _ = 1 := by norm_num
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  calc
    a ⬝ᵥ signOf σ = ∑ i, a i * signOf σ i := rfl
    _ ≤ Real.sqrt (a ⬝ᵥ a) * Real.sqrt d := hcs
    _ ≤ 1 * Real.sqrt d := mul_le_mul_of_nonneg_right hsqrta hsqrtd
    _ = Real.sqrt d := one_mul _

private theorem sSup_unitBall_cube {d n : ℕ} (hd : 0 < d)
    (σ : Fin d → Bool) :
    sSup ((fun a ↦ a ⬝ᵥ thetaXI n σ) ''
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}) =
      deltaXI d n * Real.sqrt d := by
  have hΔ : 0 ≤ deltaXI d n := by
    dsimp [deltaXI]
    positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  let u : Fin d → ℝ := fun i ↦ signOf σ i / Real.sqrt d
  have huA : u ⬝ᵥ u ≤ 1 := by
    have hsqrt_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
      Real.sq_sqrt hdR.le
    have hdot : u ⬝ᵥ u = 1 := by
      simp only [u, dotProduct]
      calc
        (∑ i, signOf σ i / Real.sqrt d *
            (signOf σ i / Real.sqrt d)) =
            ∑ _i : Fin d, (1 : ℝ) / d := by
              apply Finset.sum_congr rfl
              intro i hi
              have hs := signOf_sq σ i
              field_simp [ne_of_gt hsqrtd]
              nlinarith
        _ = 1 := by
          simp
          field_simp
    rw [hdot]
  have hudot : u ⬝ᵥ thetaXI n σ =
      deltaXI d n * Real.sqrt d := by
    have hsqrt_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
      Real.sq_sqrt hdR.le
    simp only [u, thetaXI, dotProduct]
    calc
      (∑ i, signOf σ i / Real.sqrt d *
          (deltaXI d n * signOf σ i)) =
          ∑ _i : Fin d, deltaXI d n / Real.sqrt d := by
            apply Finset.sum_congr rfl
            intro i hi
            have hs := signOf_sq σ i
            field_simp [ne_of_gt hsqrtd]
            nlinarith
      _ = deltaXI d n * Real.sqrt d := by
        simp
        field_simp [ne_of_gt hsqrtd]
        nlinarith
  have hmem :
      deltaXI d n * Real.sqrt d ∈
        (fun a ↦ a ⬝ᵥ thetaXI n σ) ''
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} :=
    ⟨u, huA, hudot⟩
  have hub : ∀ y ∈
      (fun a ↦ a ⬝ᵥ thetaXI n σ) ''
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1},
      y ≤ deltaXI d n * Real.sqrt d := by
    rintro y ⟨a, ha, rfl⟩
    have hdot := dot_sign_le_sqrt hd a ha σ
    have heq : a ⬝ᵥ thetaXI n σ =
        deltaXI d n * (a ⬝ᵥ signOf σ) := by
      simp only [thetaXI, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    change a ⬝ᵥ thetaXI n σ ≤ deltaXI d n * Real.sqrt d
    rw [heq]
    exact mul_le_mul_of_nonneg_left hdot hΔ
  have hnonempty :
      ((fun a ↦ a ⬝ᵥ thetaXI n σ) ''
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}).Nonempty := ⟨_, hmem⟩
  have hbdd : BddAbove
      ((fun a ↦ a ⬝ᵥ thetaXI n σ) ''
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}) :=
    ⟨_, hub⟩
  apply le_antisymm
  · exact csSup_le hnonempty hub
  · exact le_csSup hbdd hmem

private theorem measurableSet_allActionsMemXI {d n : ℕ}
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    MeasurableSet
      {h : LinearBanditHistory d n | ∀ t, (h t).1 ∈ A} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun t ↦
    hA.preimage (measurable_fst.comp (measurable_pi_apply t))

private theorem linearBanditMeasure_allActionsMemXI {d n : ℕ}
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy A π) :
    ∀ᵐ h ∂linearBanditMeasure θ π n, ∀ t, (h t).1 ∈ A := by
  induction n with
  | zero =>
      filter_upwards [] with h
      intro t
      exact Fin.elim0 t
  | succ n ih =>
      rw [linearBanditMeasure]
      apply (ae_map_iff
        (measurable_linearBanditHistorySnoc θ).aemeasurable
        (measurableSet_allActionsMemXI hA)).2
      have hpair :
          ∀ᵐ p ∂(linearBanditMeasure θ π n).compProd (π.select n),
            (∀ t, (p.1 t).1 ∈ A) ∧ p.2 ∈ A := by
        apply Measure.ae_compProd_of_ae_ae
        · exact (measurableSet_allActionsMemXI hA).preimage measurable_fst |>.inter
            (hA.preimage measurable_snd)
        · filter_upwards [ih] with h hh
          have ha : ∀ᵐ a ∂π.select n h, a ∈ A := by
            change A ∈ ae (π.select n h)
            rw [mem_ae_iff]
            exact hsupp n h
          filter_upwards [ha] with a ha'
          exact ⟨hh, ha'⟩
      have htriple :
          ∀ᵐ p ∂((linearBanditMeasure θ π n).compProd (π.select n)).compProd
              (Kernel.const _ (gaussianReal 0 1)),
            (∀ t, (p.1.1 t).1 ∈ A) ∧ p.1.2 ∈ A := by
        have hlift := Measure.ae_compProd_of_ae_fst
          (Kernel.const (LinearBanditHistory d n × (Fin d → ℝ))
            (gaussianReal 0 1))
          ((measurableSet_allActionsMemXI hA).preimage measurable_fst |>.inter
            (hA.preimage measurable_snd))
          hpair
        exact hlift
      filter_upwards [htriple] with p hp
      intro t
      refine Fin.lastCases ?_ (fun j ↦ ?_) t
      · simpa using hp.2
      · simpa using hp.1 j

private theorem measurable_unitBallXI {d : ℕ} :
    MeasurableSet {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} := by
  apply measurableSet_le
  · simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ ↦
      (measurable_pi_apply i).mul (measurable_pi_apply i)
  · exact measurable_const

private theorem activeXI_measurableSet {d n : ℕ} (i : Fin d) (t : Fin n) :
    MeasurableSet {h : LinearBanditHistory d n | activeXI i h t} := by
  apply measurableSet_lt
  · dsimp [activeXI]
    apply Finset.measurable_sum
    intro s hs
    exact (((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_pi_apply s))).pow_const 2)
  · exact measurable_const

private theorem lossXI_measurable {d n : ℕ} (i : Fin d) (x : ℝ) :
    Measurable (fun h : LinearBanditHistory d n ↦ lossXI i h x) := by
  dsimp [lossXI]
  apply Finset.measurable_sum
  intro t ht
  apply Measurable.ite (activeXI_measurableSet i t)
  · have ha : Measurable (fun h : LinearBanditHistory d n ↦ (h t).1 i) :=
      (measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply t))
    exact ((measurable_const.sub (ha.mul_const x)).pow_const 2)
  · exact measurable_const

private noncomputable def pathGapXI {d n : ℕ} (σ : Fin d → Bool)
    (h : LinearBanditHistory d n) : ℝ :=
  ∑ t, (deltaXI d n * Real.sqrt d - (h t).1 ⬝ᵥ thetaXI n σ)

private noncomputable def pathStoppedXI {d n : ℕ} (σ : Fin d → Bool)
    (h : LinearBanditHistory d n) : ℝ :=
  deltaXI d n * Real.sqrt d / 2 *
    ∑ i, lossXI i h (signOf σ i)

private theorem pathGapXI_measurable {d n : ℕ} (σ : Fin d → Bool) :
    Measurable (pathGapXI (n := n) σ) := by
  change Measurable (fun h : LinearBanditHistory d n ↦
    ∑ t, (deltaXI d n * Real.sqrt d -
      (h t).1 ⬝ᵥ thetaXI n σ))
  apply Finset.measurable_sum
  intro t ht
  apply Measurable.sub measurable_const
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun i _ ↦
    ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_pi_apply t))).mul_const _

private theorem pathStoppedXI_measurable {d n : ℕ} (σ : Fin d → Bool) :
    Measurable (pathStoppedXI (n := n) σ) := by
  change Measurable (fun h : LinearBanditHistory d n ↦
    deltaXI d n * Real.sqrt d / 2 *
      ∑ i, lossXI i h (signOf σ i))
  exact measurable_const.mul
    (Finset.measurable_sum _ fun i _ ↦
      lossXI_measurable i (signOf σ i))

private theorem pathGapXI_ge_pathStoppedXI {d n : ℕ} (hd : 0 < d)
    (σ : Fin d → Bool) (h : LinearBanditHistory d n)
    (ha : ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1) :
    pathStoppedXI σ h ≤ pathGapXI σ h := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hsqrtd_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
    Real.sq_sqrt hdR.le
  have hΔ : 0 ≤ deltaXI d n := by
    dsimp [deltaXI]
    positivity
  have hcoef : 0 ≤ deltaXI d n * Real.sqrt d / 2 := by positivity
  let full : Fin n → Fin d → ℝ := fun t i ↦
    (1 / Real.sqrt d - (h t).1 i * signOf σ i) ^ 2
  have hfull_round (t : Fin n) :
      deltaXI d n * Real.sqrt d / 2 * (∑ i, full t i) ≤
        deltaXI d n * Real.sqrt d -
          (h t).1 ⬝ᵥ thetaXI n σ := by
    have hsum :
        (∑ i, full t i) =
          1 + (h t).1 ⬝ᵥ (h t).1 -
            2 / Real.sqrt d * ((h t).1 ⬝ᵥ signOf σ) := by
      simp only [full, dotProduct]
      calc
        (∑ i, (1 / Real.sqrt d -
            (h t).1 i * signOf σ i) ^ 2) =
            ∑ i, ((1 / Real.sqrt d) ^ 2 +
              (h t).1 i ^ 2 -
              2 / Real.sqrt d * ((h t).1 i * signOf σ i)) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hs := signOf_sq σ i
                calc
                  (1 / Real.sqrt d -
                      (h t).1 i * signOf σ i) ^ 2 =
                      (1 / Real.sqrt d) ^ 2 +
                        ((h t).1 i * signOf σ i) ^ 2 -
                        2 / Real.sqrt d *
                          ((h t).1 i * signOf σ i) := by ring
                  _ = (1 / Real.sqrt d) ^ 2 + (h t).1 i ^ 2 -
                      2 / Real.sqrt d *
                        ((h t).1 i * signOf σ i) := by
                        rw [mul_pow, hs, mul_one]
        _ = (d : ℝ) * (1 / Real.sqrt d) ^ 2 +
              ∑ i, (h t).1 i ^ 2 -
              2 / Real.sqrt d * ∑ i, ((h t).1 i * signOf σ i) := by
                simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                  Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul, Finset.mul_sum]
        _ = 1 + (∑ i, (h t).1 i * (h t).1 i) -
              2 / Real.sqrt d *
                (∑ i, (h t).1 i * signOf σ i) := by
              have hrootne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsqrtd
              field_simp [hrootne]
              nlinarith
    have hsumle :
        (∑ i, full t i) ≤
          2 - 2 / Real.sqrt d * ((h t).1 ⬝ᵥ signOf σ) := by
      rw [hsum]
      linarith [ha t]
    have hscaled := mul_le_mul_of_nonneg_left hsumle hcoef
    have htheta :
        (h t).1 ⬝ᵥ thetaXI n σ =
          deltaXI d n * ((h t).1 ⬝ᵥ signOf σ) := by
      simp only [thetaXI, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [htheta]
    calc
      deltaXI d n * Real.sqrt d / 2 * (∑ i, full t i)
          ≤ deltaXI d n * Real.sqrt d / 2 *
            (2 - 2 / Real.sqrt d *
              ((h t).1 ⬝ᵥ signOf σ)) := hscaled
      _ = deltaXI d n * Real.sqrt d -
          deltaXI d n * ((h t).1 ⬝ᵥ signOf σ) := by
            field_simp [ne_of_gt hsqrtd]
  have hloss_full :
      (∑ i, lossXI i h (signOf σ i)) ≤
        ∑ t, ∑ i, full t i := by
    calc
      (∑ i, lossXI i h (signOf σ i)) =
          ∑ i, ∑ t, if activeXI i h t then full t i else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = ∑ t, ∑ i, if activeXI i h t then full t i else 0 := by
            rw [Finset.sum_comm]
      _ ≤ ∑ t, ∑ i, full t i := by
            apply Finset.sum_le_sum
            intro t ht
            apply Finset.sum_le_sum
            intro i hi
            by_cases hactive : activeXI i h t
            · simp [hactive]
            · simp [hactive, full]
              positivity
  have hloss_scaled := mul_le_mul_of_nonneg_left hloss_full hcoef
  calc
    pathStoppedXI σ h =
        deltaXI d n * Real.sqrt d / 2 *
          (∑ i, lossXI i h (signOf σ i)) := rfl
    _ ≤ deltaXI d n * Real.sqrt d / 2 *
        (∑ t, ∑ i, full t i) := hloss_scaled
    _ = ∑ t, deltaXI d n * Real.sqrt d / 2 *
        (∑ i, full t i) := by rw [Finset.mul_sum]
    _ ≤ ∑ t, (deltaXI d n * Real.sqrt d -
        (h t).1 ⬝ᵥ thetaXI n σ) := by
          exact Finset.sum_le_sum fun t ht ↦ hfull_round t
    _ = pathGapXI σ h := rfl

private theorem abs_dot_sign_le_sqrt {d : ℕ} (hd : 0 < d)
    (a : Fin d → ℝ) (ha : a ⬝ᵥ a ≤ 1) (σ : Fin d → Bool) :
    |a ⬝ᵥ signOf σ| ≤ Real.sqrt d := by
  rw [abs_le]
  constructor
  · have hneg := dot_sign_le_sqrt hd (-a) (by
      simpa [dotProduct] using ha) σ
    have hneg' : -(a ⬝ᵥ signOf σ) ≤ Real.sqrt d := by
      simpa [dotProduct] using hneg
    linarith
  · exact dot_sign_le_sqrt hd a ha σ

private theorem actionTheta_integrable {d n : ℕ} (hd : 0 < d)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (t : Fin n) :
    Integrable
      (fun h : LinearBanditHistory d n ↦
        (h t).1 ⬝ᵥ thetaXI n σ)
      (linearBanditMeasure (thetaXI n σ) π n) := by
  let C : ℝ := deltaXI d n * Real.sqrt d
  have hC : 0 ≤ C := by
    dsimp [C, deltaXI]
    positivity
  apply Integrable.of_mem_Icc (-C) C
  · simp only [dotProduct]
    exact (Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply t))).mul_const _).aemeasurable
  · filter_upwards [
      linearBanditMeasure_allActionsMemXI
        measurable_unitBallXI (thetaXI n σ) π hsupp] with h hh
    have habs := abs_dot_sign_le_sqrt hd (h t).1 (hh t) σ
    have hΔ : 0 ≤ deltaXI d n := by
      dsimp [deltaXI]
      positivity
    have htheta :
        (h t).1 ⬝ᵥ thetaXI n σ =
          deltaXI d n * ((h t).1 ⬝ᵥ signOf σ) := by
      simp only [thetaXI, dotProduct]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [htheta]
    have hscaled := mul_le_mul_of_nonneg_left habs hΔ
    have habsTheta :
        |deltaXI d n * ((h t).1 ⬝ᵥ signOf σ)| ≤
          deltaXI d n * Real.sqrt d := by
      rw [abs_mul, abs_of_nonneg hΔ]
      exact hscaled
    exact abs_le.mp habsTheta

private theorem pathStopped_expected_le_regret {d n : ℕ}
    (hd : 0 < d) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) :
    (∫ h, pathStoppedXI σ h
        ∂linearBanditMeasure (thetaXI n σ) π n) ≤
      linearBanditExpectedRegret
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
        (thetaXI n σ) π n := by
  let μ := linearBanditMeasure (thetaXI n σ) π n
  let dots : LinearBanditHistory d n → ℝ := fun h ↦
    ∑ t, (h t).1 ⬝ᵥ thetaXI n σ
  have hdotsInt : Integrable dots μ := by
    dsimp [dots, μ]
    exact integrable_finset_sum Finset.univ fun t ht ↦
      actionTheta_integrable hd π hsupp σ t
  have hgapInt : Integrable (pathGapXI σ) μ := by
    have hconst : Integrable
        (fun _ : LinearBanditHistory d n ↦
          (n : ℝ) * (deltaXI d n * Real.sqrt d)) μ :=
      integrable_const _
    have heq : pathGapXI σ =
        fun h ↦ (n : ℝ) * (deltaXI d n * Real.sqrt d) - dots h := by
      funext h
      simp only [pathGapXI, dots, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [heq]
    exact hconst.sub hdotsInt
  have hstopped_nonneg (h : LinearBanditHistory d n) :
      0 ≤ pathStoppedXI σ h := by
    dsimp [pathStoppedXI, deltaXI, lossXI]
    positivity
  have hstoppedInt : Integrable (pathStoppedXI σ) μ := by
    apply hgapInt.mono_nonneg
    · exact (pathStoppedXI_measurable σ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall hstopped_nonneg
    · filter_upwards [
        linearBanditMeasure_allActionsMemXI
          measurable_unitBallXI (thetaXI n σ) π hsupp] with h hh
      exact pathGapXI_ge_pathStoppedXI hd σ h hh
  have hint :
      (∫ h, pathStoppedXI σ h ∂μ) ≤
        ∫ h, pathGapXI σ h ∂μ := by
    apply integral_mono_ae hstoppedInt hgapInt
    filter_upwards [
      linearBanditMeasure_allActionsMemXI
        measurable_unitBallXI (thetaXI n σ) π hsupp] with h hh
    exact pathGapXI_ge_pathStoppedXI hd σ h hh
  calc
    (∫ h, pathStoppedXI σ h
        ∂linearBanditMeasure (thetaXI n σ) π n)
        ≤ ∫ h, pathGapXI σ h ∂μ := by simpa [μ] using hint
    _ = (n : ℝ) * (deltaXI d n * Real.sqrt d) -
        ∫ h, dots h ∂μ := by
          have heq : pathGapXI σ =
              fun h ↦ (n : ℝ) * (deltaXI d n * Real.sqrt d) -
                dots h := by
            funext h
            simp only [pathGapXI, dots, Finset.sum_sub_distrib,
              Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
          rw [heq, integral_sub (integrable_const _) hdotsInt]
          simp
    _ = linearBanditExpectedRegret
        {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
        (thetaXI n σ) π n := by
          rw [linearBanditExpectedRegret, sSup_unitBall_cube hd σ]

private noncomputable def energyXI {d n : ℕ} (i : Fin d)
    (h : LinearBanditHistory d n) : ℝ :=
  ∑ t, if activeXI i h t then ((h t).1 i) ^ 2 else 0

private theorem coordinate_sq_le_oneXI {d : ℕ}
    (a : Fin d → ℝ) (ha : a ⬝ᵥ a ≤ 1) (i : Fin d) :
    a i ^ 2 ≤ 1 := by
  have hterm : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (fun j hj ↦ sq_nonneg (a j))
      (Finset.mem_univ i)
  have hsum : (∑ j, a j ^ 2) = a ⬝ᵥ a := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum] at hterm
  exact hterm.trans ha

private theorem energyXI_le {d n : ℕ} (hd : 0 < d)
    (h : LinearBanditHistory d n) (i : Fin d)
    (ha : ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1) :
    energyXI i h ≤ (n : ℝ) / d + 1 := by
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun t ↦ activeXI i h t)
  have hx (t : Fin n) : ((h t).1 i) ^ 2 ≤ 1 :=
    coordinate_sq_le_oneXI (h t).1 (ha t) i
  have hx0 (t : Fin n) : 0 ≤ ((h t).1 i) ^ 2 := sq_nonneg _
  have hstop : energyXI i h =
      ∑ t ∈ S, ((h t).1 i) ^ 2 := by
    dsimp [energyXI, S]
    rw [Finset.sum_filter]
  rw [hstop]
  by_cases hSne : S.Nonempty
  · let m : Fin n := S.max' hSne
    have hmS : m ∈ S := Finset.max'_mem S hSne
    have hSm : ∀ t ∈ S, t ≤ m := fun t ht ↦ Finset.le_max' S t ht
    let I : Finset (Fin n) := Finset.univ.filter (fun t ↦ t ≤ m)
    have hSI : S ⊆ I := by
      intro t ht
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hSm t ht
    have hsumle : (∑ t ∈ S, ((h t).1 i) ^ 2) ≤
        ∑ t ∈ I, ((h t).1 i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hSI
        (fun t htI htS ↦ hx0 t)
    have hmactive : activeXI i h m := by simpa [S] using hmS
    have hsplit :
        (∑ t ∈ I, ((h t).1 i) ^ 2) =
          (∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s < m),
            ((h s).1 i) ^ 2) + ((h m).1 i) ^ 2 := by
      have hI :
          I = insert m
            (Finset.univ.filter (fun t : Fin n ↦ t < m)) := by
        ext t
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        omega
      rw [hI, Finset.sum_insert]
      · ring
      · simp
    rw [hsplit] at hsumle
    calc
      ∑ t ∈ S, ((h t).1 i) ^ 2 ≤
          (∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s < m),
            ((h s).1 i) ^ 2) + ((h m).1 i) ^ 2 := hsumle
      _ ≤ (n : ℝ) / d + 1 :=
        add_le_add hmactive.le (hx m)
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    rw [hSempty]
    simp
    positivity

private theorem lossXI_le {d n : ℕ} (hd : 0 < d)
    (h : LinearBanditHistory d n) (i : Fin d) (x : ℝ)
    (hxsign : x ^ 2 = 1)
    (ha : ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1) :
    lossXI i h x ≤ 4 * (n : ℝ) / d + 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hsqrt_sq : Real.sqrt (d : ℝ) ^ 2 = d := Real.sq_sqrt hdR.le
  have hterm (t : Fin n) :
      (if activeXI i h t then
          (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0) ≤
        2 / d + 2 * (if activeXI i h t then ((h t).1 i) ^ 2 else 0) := by
    by_cases ht : activeXI i h t
    · simp only [if_pos ht]
      have hsq := sq_nonneg (1 / Real.sqrt d + (h t).1 i * x)
      have hrootne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsqrt
      have hc : (1 / Real.sqrt (d : ℝ)) ^ 2 = 1 / d := by
        field_simp [hrootne]
        exact hsqrt_sq.symm
      have hb : ((h t).1 i * x) ^ 2 = ((h t).1 i) ^ 2 := by
        rw [mul_pow, hxsign, mul_one]
      have hid :
          (1 / Real.sqrt d - (h t).1 i * x) ^ 2 +
              (1 / Real.sqrt d + (h t).1 i * x) ^ 2 =
            2 * (1 / Real.sqrt d) ^ 2 +
              2 * ((h t).1 i * x) ^ 2 := by ring
      calc
        (1 / Real.sqrt d - (h t).1 i * x) ^ 2
            ≤ 2 * (1 / Real.sqrt d) ^ 2 +
                2 * ((h t).1 i * x) ^ 2 := by nlinarith
        _ = 2 / d + 2 * ((h t).1 i) ^ 2 := by rw [hc, hb]; ring
    · simp only [if_neg ht]
      positivity
  calc
    lossXI i h x ≤ ∑ t : Fin n,
        (2 / d + 2 *
          (if activeXI i h t then ((h t).1 i) ^ 2 else 0)) := by
      dsimp [lossXI]
      exact Finset.sum_le_sum fun t ht ↦ hterm t
    _ = 2 * (n : ℝ) / d + 2 * energyXI i h := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Finset.mul_sum, energyXI]
      ring
    _ ≤ 2 * (n : ℝ) / d + 2 * ((n : ℝ) / d + 1) := by
      gcongr
      exact energyXI_le hd h i ha
    _ = 4 * (n : ℝ) / d + 2 := by ring

private theorem lossXI_integrable_any {d n : ℕ} (hd : 0 < d)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) (x : ℝ) (hx : x ^ 2 = 1) :
    Integrable (fun h : LinearBanditHistory d n ↦
      lossXI i h x)
      (linearBanditMeasure (thetaXI n σ) π n) := by
  apply Integrable.of_mem_Icc 0 (4 * (n : ℝ) / d + 2)
  · exact (lossXI_measurable i x).aemeasurable
  · filter_upwards [
      linearBanditMeasure_allActionsMemXI
        measurable_unitBallXI (thetaXI n σ) π hsupp] with h hh
    constructor
    · dsimp [lossXI]
      positivity
    · exact lossXI_le hd h i x hx hh

private theorem lossXI_integrable {d n : ℕ} (hd : 0 < d)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    Integrable (fun h : LinearBanditHistory d n ↦
      lossXI i h (signOf σ i))
      (linearBanditMeasure (thetaXI n σ) π n) :=
  lossXI_integrable_any hd π hsupp σ i (signOf σ i) (signOf_sq σ i)

private theorem activeCoverageXI {d n : ℕ} (hd : 0 < d)
    (h : LinearBanditHistory d n) (i : Fin d) :
    (n : ℝ) / d ≤
      ((Finset.univ.filter (fun t : Fin n ↦ activeXI i h t)).card : ℝ) / d +
        energyXI i h := by
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun t ↦ activeXI i h t)
  have henergy :
      energyXI i h = ∑ t ∈ S, ((h t).1 i) ^ 2 := by
    dsimp [energyXI, S]
    rw [Finset.sum_filter]
  change (n : ℝ) / d ≤ (S.card : ℝ) / d + energyXI i h
  rw [henergy]
  by_cases hSuniv : S = Finset.univ
  · rw [hSuniv]
    have hnonneg :
        0 ≤ ∑ t : Fin n, ((h t).1 i) ^ 2 :=
      Finset.sum_nonneg fun t ht ↦ sq_nonneg _
    simpa using
      (le_add_of_nonneg_right hnonneg :
        (n : ℝ) / d ≤ (n : ℝ) / d +
          ∑ t : Fin n, ((h t).1 i) ^ 2)
  · let T : Finset (Fin n) := Finset.univ \ S
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hTempty
      apply hSuniv
      ext t
      have htU : t ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ t
      have : t ∉ T := by simp [hTempty]
      simpa [T] using this
    let m : Fin n := T.min' hTne
    have hmT : m ∈ T := Finset.min'_mem T hTne
    have hmnotS : m ∉ S := (Finset.mem_sdiff.mp hmT).2
    have hmin : ∀ t ∈ T, m ≤ t := fun t ht ↦ Finset.min'_le T t ht
    have hbefore (t : Fin n) (htm : t < m) : t ∈ S := by
      by_contra htS
      have htT : t ∈ T := by simp [T, htS]
      exact (not_le_of_gt htm) (hmin t htT)
    have hnotactive : ¬ activeXI i h m := by
      simpa [S] using hmnotS
    have hprefix :
        (n : ℝ) / d ≤
          ∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t < m),
            ((h t).1 i) ^ 2 := le_of_not_gt hnotactive
    have hsubset :
        Finset.univ.filter (fun t : Fin n ↦ t < m) ⊆ S := by
      intro t ht
      exact hbefore t (by simpa using ht)
    have hprefix_le :
        (∑ t ∈ Finset.univ.filter (fun t : Fin n ↦ t < m),
            ((h t).1 i) ^ 2) ≤
          ∑ t ∈ S, ((h t).1 i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun t htS htpre ↦ sq_nonneg _)
    have hE : (n : ℝ) / d ≤
        ∑ t ∈ S, ((h t).1 i) ^ 2 := hprefix.trans hprefix_le
    have hcard_nonneg :
        0 ≤ ((S.card : ℕ) : ℝ) / d := by positivity
    exact hE.trans (le_add_of_nonneg_left hcard_nonneg)

private theorem lossXI_pair_pointwise {d n : ℕ} (hd : 0 < d)
    (h : LinearBanditHistory d n) (i : Fin d) (x : ℝ)
    (hx : x ^ 2 = 1) :
    2 * (n : ℝ) / d ≤ lossXI i h x + lossXI i h (-x) := by
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun t ↦ activeXI i h t)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hsqrtd_sq : Real.sqrt (d : ℝ) ^ 2 = d :=
    Real.sq_sqrt hdR.le
  have hpair :
      lossXI i h x + lossXI i h (-x) =
        2 * (S.card : ℝ) / d + 2 * energyXI i h := by
    have hone (t : Fin n) :
        (1 / Real.sqrt d - (h t).1 i * x) ^ 2 +
            (1 / Real.sqrt d - (h t).1 i * (-x)) ^ 2 =
          2 / d + 2 * ((h t).1 i) ^ 2 := by
      have hrootne : Real.sqrt (d : ℝ) ≠ 0 := ne_of_gt hsqrtd
      have hc : (1 / Real.sqrt (d : ℝ)) ^ 2 = 1 / d := by
        field_simp [hrootne]
        exact hsqrtd_sq.symm
      have hax : ((h t).1 i * x) ^ 2 = ((h t).1 i) ^ 2 := by
        rw [mul_pow, hx, mul_one]
      rw [show (h t).1 i * (-x) = -((h t).1 i * x) by ring]
      rw [sub_neg_eq_add]
      have hid :
          (1 / Real.sqrt d - (h t).1 i * x) ^ 2 +
              (1 / Real.sqrt d + (h t).1 i * x) ^ 2 =
            2 * (1 / Real.sqrt d) ^ 2 +
              2 * ((h t).1 i * x) ^ 2 := by ring
      rw [hc, hax] at hid
      simpa [div_eq_mul_inv] using hid
    have henergyEq :
        energyXI i h = ∑ t ∈ S, ((h t).1 i) ^ 2 := by
      dsimp [energyXI, S]
      rw [Finset.sum_filter]
    calc
      lossXI i h x + lossXI i h (-x) =
          ∑ t, ((if activeXI i h t then
              (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0) +
            (if activeXI i h t then
              (1 / Real.sqrt d - (h t).1 i * (-x)) ^ 2 else 0)) := by
                dsimp [lossXI]
                rw [← Finset.sum_add_distrib]
      _ = ∑ t ∈ S, (2 / d + 2 * ((h t).1 i) ^ 2) := by
            dsimp [S]
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro t ht
            by_cases hactive : activeXI i h t
            · simpa [hactive] using hone t
            · simp [hactive]
      _ = 2 * (S.card : ℝ) / d + 2 * energyXI i h := by
            rw [henergyEq]
            simp only [Finset.sum_add_distrib, Finset.sum_const,
              nsmul_eq_mul, Finset.mul_sum]
            ring
  rw [hpair]
  have hcov := activeCoverageXI hd h i
  change (n : ℝ) / d ≤ (S.card : ℝ) / d + energyXI i h at hcov
  have hcov2 := mul_le_mul_of_nonneg_left hcov (by norm_num : (0 : ℝ) ≤ 2)
  calc
    2 * (n : ℝ) / d = 2 * ((n : ℝ) / d) := by ring
    _ ≤ 2 * ((S.card : ℝ) / d + energyXI i h) := hcov2
    _ = 2 * (S.card : ℝ) / d + 2 * energyXI i h := by ring

private def flipEquivXI {d : ℕ} (i : Fin d) :
    (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun σ := Function.update σ i (!(σ i))
  invFun σ := Function.update σ i (!(σ i))
  left_inv σ := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  right_inv σ := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]

private theorem correctionXI_le {d n : ℕ} (hd : 0 < d)
    (hn : 0 < n) (hdn : d ≤ 2 * n) :
    deltaXI d n / 2 * (4 * (n : ℝ) / d + 2) *
        Real.sqrt ((n : ℝ) / d + 1) ≤
      (n : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let q : ℝ := (n : ℝ) / d
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqhalf : (1 / 2 : ℝ) ≤ q := by
    have hdnR : (d : ℝ) ≤ 2 * n := by exact_mod_cast hdn
    dsimp [q]
    apply (le_div_iff₀ hdR).2
    nlinarith
  have hlin : 4 * q + 2 ≤ 8 * q := by nlinarith
  have hsqrtarg : q + 1 ≤ 3 * q := by nlinarith
  have hsqrtle :
      Real.sqrt (q + 1) ≤ Real.sqrt (3 * q) :=
    Real.sqrt_le_sqrt hsqrtarg
  have hΔ : 0 ≤ deltaXI d n := by
    dsimp [deltaXI]
    positivity
  have hsqrtq : 0 ≤ Real.sqrt (q + 1) := Real.sqrt_nonneg _
  have hsqrt3q : 0 ≤ Real.sqrt (3 * q) := Real.sqrt_nonneg _
  have hfirst :
      deltaXI d n / 2 * (4 * q + 2) * Real.sqrt (q + 1) ≤
        deltaXI d n / 2 * (8 * q) * Real.sqrt (3 * q) := by
    have hfac : 0 ≤ deltaXI d n / 2 := by positivity
    calc
      deltaXI d n / 2 * (4 * q + 2) * Real.sqrt (q + 1)
          ≤ deltaXI d n / 2 * (8 * q) * Real.sqrt (q + 1) := by
            gcongr
      _ ≤ deltaXI d n / 2 * (8 * q) * Real.sqrt (3 * q) := by
            gcongr
  have hΔsq :
      deltaXI d n ^ 2 = (d : ℝ) / (48 * n) := by
    dsimp [deltaXI]
    exact Real.sq_sqrt (by positivity)
  have hsqrt3q_sq : Real.sqrt (3 * q) ^ 2 = 3 * q :=
    Real.sq_sqrt (by positivity)
  have hfactor_nonneg :
      0 ≤ 4 * deltaXI d n * Real.sqrt (3 * q) := by positivity
  have hfactor_sq :
      (4 * deltaXI d n * Real.sqrt (3 * q)) ^ 2 = 1 := by
    rw [mul_pow, mul_pow, hΔsq, hsqrt3q_sq]
    dsimp [q]
    field_simp [ne_of_gt hdR, ne_of_gt hnR]
    ring
  have hfactor :
      4 * deltaXI d n * Real.sqrt (3 * q) = 1 := by
    nlinarith
  have hgoal :
      deltaXI d n / 2 * (4 * q + 2) *
          Real.sqrt (q + 1) ≤ q := by
    calc
    deltaXI d n / 2 * (4 * q + 2) *
        Real.sqrt (q + 1) ≤
      deltaXI d n / 2 * (8 * q) * Real.sqrt (3 * q) := hfirst
    _ = q * (4 * deltaXI d n * Real.sqrt (3 * q)) := by ring
    _ = q * 1 := by rw [hfactor]
    _ = q := by ring
  calc
    deltaXI d n / 2 * (4 * (n : ℝ) / d + 2) *
          Real.sqrt ((n : ℝ) / d + 1) =
        deltaXI d n / 2 * (4 * ((n : ℝ) / d) + 2) *
          Real.sqrt ((n : ℝ) / d + 1) := by ring
    _ ≤ (n : ℝ) / d := by simpa only [q] using hgoal

private theorem coordinateFlipPairXI {d n : ℕ}
    (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    (n : ℝ) / d ≤
      (∫ h, lossXI i h (signOf σ i)
        ∂linearBanditMeasure (thetaXI n σ) π n) +
      ∫ h, lossXI i h
          (signOf ((flipEquivXI i) σ) i)
        ∂linearBanditMeasure (thetaXI n ((flipEquivXI i) σ)) π n := by
  have hn : 0 < n := by omega
  let σ' : Fin d → Bool := (flipEquivXI i) σ
  let P := linearBanditMeasure (thetaXI n σ) π n
  let Q := linearBanditMeasure (thetaXI n σ') π n
  let s : ℝ := signOf σ i
  let c : ℝ :=
    deltaXI d n / 2 * (4 * (n : ℝ) / d + 2) *
      Real.sqrt ((n : ℝ) / d + 1)
  have hs : s ^ 2 = 1 := by
    dsimp [s]
    exact signOf_sq σ i
  have hsflip : signOf σ' i = -s := by
    dsimp [σ', s, flipEquivXI]
    exact signOf_flip σ i
  have hchange :
      (∫ h, lossXI i h s ∂Q) - c ≤
        ∫ h, lossXI i h s ∂P := by
    simpa only [deltaXI, thetaXI, signOf, activeXI, lossXI,
      flipEquivXI, σ', P, Q, s, c] using
      linear_bandit_unit_ball_stopped_loss_change_of_measure
        hd hdn π hsupp σ i
  have hc : c ≤ (n : ℝ) / d := by
    dsimp [c]
    exact correctionXI_le hd hn hdn
  have hUs : Integrable
      (fun h : LinearBanditHistory d n ↦ lossXI i h s) Q := by
    dsimp [Q]
    exact lossXI_integrable_any hd π hsupp σ' i s hs
  have hUflip : Integrable
      (fun h : LinearBanditHistory d n ↦ lossXI i h (signOf σ' i)) Q := by
    dsimp [Q]
    exact lossXI_integrable hd π hsupp σ' i
  have hpair :
      2 * (n : ℝ) / d ≤
        (∫ h, lossXI i h s ∂Q) +
          ∫ h, lossXI i h (signOf σ' i) ∂Q := by
    rw [← integral_add hUs hUflip]
    calc
      2 * (n : ℝ) / d =
          ∫ _h : LinearBanditHistory d n, 2 * (n : ℝ) / d ∂Q := by
            simp
      _ ≤ ∫ h, (lossXI i h s + lossXI i h (signOf σ' i)) ∂Q := by
        apply integral_mono (integrable_const _) (hUs.add hUflip)
        intro h
        rw [hsflip]
        exact lossXI_pair_pointwise hd h i s hs
  dsimp [P, Q, σ', s] at hchange hpair ⊢
  dsimp [c] at hc hchange
  ring_nf at hchange hc hpair ⊢
  linarith

end BanditAlgorithm

open BanditAlgorithm

theorem solution {d n : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    (Fintype.card (Fin d → Bool) : ℝ) *
          (n * Δ * Real.sqrt d / 4) ≤
      ∑ σ : Fin d → Bool,
        linearBanditExpectedRegret
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
          (fun i ↦ Δ * if σ i then 1 else -1) π n := by
  classical
  have hn : 0 < n := by omega
  let E : (Fin d → Bool) → Fin d → ℝ := fun σ i ↦
    ∫ h, lossXI i h (signOf σ i)
      ∂linearBanditMeasure (thetaXI n σ) π n
  let R : (Fin d → Bool) → ℝ := fun σ ↦
    linearBanditExpectedRegret
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
      (thetaXI n σ) π n
  let C : ℝ := deltaXI d n * Real.sqrt d / 2
  have hC : 0 ≤ C := by
    dsimp [C, deltaXI]
    positivity
  have hreg (σ : Fin d → Bool) : C * (∑ i, E σ i) ≤ R σ := by
    have hbase := pathStopped_expected_le_regret (n := n) hd π hsupp σ
    have hint :
        (∫ h, pathStoppedXI σ h
          ∂linearBanditMeasure (thetaXI n σ) π n) =
          C * ∑ i, E σ i := by
      change
        (∫ h, C * (∑ i, lossXI i h (signOf σ i))
          ∂linearBanditMeasure (thetaXI n σ) π n) =
          C * ∑ i, E σ i
      rw [integral_const_mul]
      rw [integral_finset_sum]
      intro i hi
      exact lossXI_integrable hd π hsupp σ i
    rw [hint] at hbase
    exact hbase
  have hpair (σ : Fin d → Bool) (i : Fin d) :
      (n : ℝ) / d ≤ E σ i + E ((flipEquivXI i) σ) i := by
    exact coordinateFlipPairXI hd hdn π hsupp σ i
  have hflipSum (i : Fin d) :
      (∑ σ : Fin d → Bool, E ((flipEquivXI i) σ) i) =
        ∑ σ : Fin d → Bool, E σ i := by
    exact (flipEquivXI i).sum_comp (fun σ ↦ E σ i)
  have hcoord (i : Fin d) :
      (Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / (2 * d) ≤
        ∑ σ : Fin d → Bool, E σ i := by
    have hsum :
        (∑ _σ : Fin d → Bool, (n : ℝ) / d) ≤
          ∑ σ : Fin d → Bool, (E σ i + E ((flipEquivXI i) σ) i) :=
      Finset.sum_le_sum fun σ hσ ↦ hpair σ i
    rw [Finset.sum_add_distrib, hflipSum] at hsum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    have hsum' :
        (Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / d ≤
          2 * (∑ σ : Fin d → Bool, E σ i) := by
      convert hsum using 1 <;> ring
    calc
      (Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / (2 * d) =
          ((Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / d) / 2 := by
            ring
      _ ≤ (2 * (∑ σ : Fin d → Bool, E σ i)) / 2 :=
        div_le_div_of_nonneg_right hsum' (by norm_num)
      _ = ∑ σ : Fin d → Bool, E σ i := by ring
  have henergy :
      (Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / 2 ≤
        ∑ σ : Fin d → Bool, ∑ i : Fin d, E σ i := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
      hcoord i)
    rw [Finset.sum_comm]
    calc
      (Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / 2 =
          ∑ _i : Fin d,
            (Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / (2 * d) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
              have hdR : (0 : ℝ) < d := by exact_mod_cast hd
              field_simp [ne_of_gt hdR]
      _ ≤ ∑ i : Fin d, ∑ σ : Fin d → Bool, E σ i := hs
  have hscaled := mul_le_mul_of_nonneg_left henergy hC
  have hsumReg :
      C * (∑ σ : Fin d → Bool, ∑ i : Fin d, E σ i) ≤
        ∑ σ : Fin d → Bool, R σ := by
    calc
      C * (∑ σ : Fin d → Bool, ∑ i : Fin d, E σ i) =
          ∑ σ : Fin d → Bool, C * (∑ i : Fin d, E σ i) := by
            rw [Finset.mul_sum]
      _ ≤ ∑ σ : Fin d → Bool, R σ :=
        Finset.sum_le_sum fun σ hσ ↦ hreg σ
  calc
    (Fintype.card (Fin d → Bool) : ℝ) *
          (n * Real.sqrt ((d : ℝ) / (48 * n)) *
            Real.sqrt d / 4) =
        C * ((Fintype.card (Fin d → Bool) : ℝ) * (n : ℝ) / 2) := by
          dsimp [C, deltaXI]
          ring
    _ ≤ C * (∑ σ : Fin d → Bool, ∑ i : Fin d, E σ i) := hscaled
    _ ≤ ∑ σ : Fin d → Bool, R σ := hsumReg
    _ = ∑ σ : Fin d → Bool,
        linearBanditExpectedRegret
          {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1}
          (fun i ↦ Real.sqrt ((d : ℝ) / (48 * n)) *
            if σ i then 1 else -1) π n := by
          rfl
