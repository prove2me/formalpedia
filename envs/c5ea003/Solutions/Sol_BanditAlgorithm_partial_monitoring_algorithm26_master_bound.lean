-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_algorithm26_master_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:29:37.004045+00:00
-- url     : https://prove2.me/submissions/acf6edd5-e979-40b4-bcd2-99f227aaeefc

import Definitions.Def_PartialMonitoringAlgorithm26
import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_BanditAlgorithm_expWeights_psi_regret_on_finset
import Theorems.Thm_BanditAlgorithm_integral_pmOutcomeMeasure
import Theorems.Thm_BanditAlgorithm_pmVectorEstimator_importance_weighted_gap
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

noncomputable section

private noncomputable def pmAlgorithm26State
    {k : ℕ} {𝕊 : Type*}
    (pOf : (Fin k → ℝ) → Fin k → ℝ)
    (fOf : (Fin k → ℝ) → Fin k → 𝕊 → Fin k → ℝ) :
    (t : ℕ) → PMHistory k 𝕊 t → (Fin k → ℝ)
  | 0, _ => fun _ => 0
  | t + 1, h =>
      let x := pmAlgorithm26State pOf fOf t (Fin.init h)
      let obs := h (Fin.last t)
      fun b => x b + fOf x obs.1 obs.2 b / pOf x obs.1

private def pmHistoryPrefix
    {k n : ℕ} {𝕊 : Type*} (t : ℕ) (ht : t ≤ n)
    (h : PMHistory k 𝕊 n) : PMHistory k 𝕊 t :=
  fun s => h (Fin.castLE ht s)

private lemma integral_pm_adapted_sum
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (i : Fin n → Fin d)
    (F : (t : ℕ) → PMHistory k 𝕊 t → (Fin k × 𝕊) → ℝ) :
    (∫ h, ∑ t : Fin n,
        F t (pmHistoryPrefix t t.isLt.le h) (h t) ∂pmMeasure G π n i) =
      ∑ t : Fin n,
        ∫ h, ∫ z, F t h z ∂pmStepKernel G π (i t) t h
          ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s)) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      let i0 : Fin n → Fin d := fun t => i t.castSucc
      let j : Fin d := i (Fin.last n)
      let snocFn : PMHistory k 𝕊 n × (Fin k × 𝕊) → PMHistory k 𝕊 (n + 1) :=
        fun p => Fin.snoc p.1 p.2
      let H : PMHistory k 𝕊 (n + 1) → ℝ := fun h =>
        ∑ t : Fin (n + 1), F t (pmHistoryPrefix t t.isLt.le h) (h t)
      have hH : Measurable H := measurable_of_countable _
      have hsnoc : Measurable snocFn := measurable_pmHistorySnoc
      rw [pmMeasure]
      change (∫ h, H h ∂Measure.map snocFn
          ((pmMeasure G π n i0).compProd (pmStepKernel G π j n))) = _
      rw [MeasureTheory.integral_map hsnoc.aemeasurable hH.aestronglyMeasurable]
      have hsplit (p : PMHistory k 𝕊 n × (Fin k × 𝕊)) :
          H (snocFn p) =
            (∑ t : Fin n, F t (pmHistoryPrefix t t.isLt.le p.1) (p.1 t)) +
              F n p.1 p.2 := by
        dsimp [H, snocFn]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        congr 1
        · apply Finset.sum_congr rfl
          intro t ht
          congr 1
          funext s
          unfold pmHistoryPrefix
          let r : Fin n := Fin.castLE t.isLt.le s
          have hsL : Fin.castLE t.castSucc.isLt.le s = r.castSucc := by
            apply Fin.ext
            rfl
          rw [hsL, Fin.snoc_castSucc]
        · congr 1
          funext s
          unfold pmHistoryPrefix
          let r : Fin n := ⟨s, by simpa using s.isLt⟩
          have hsL : Fin.castLE (Fin.last n).isLt.le s = r.castSucc := by
            apply Fin.ext
            rfl
          rw [hsL, Fin.snoc_castSucc]
          congr
      simp_rw [hsplit]
      have hpreInt : Integrable (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
          ∑ t : Fin n, F t (pmHistoryPrefix t t.isLt.le p.1) (p.1 t))
          ((pmMeasure G π n i0).compProd (pmStepKernel G π j n)) :=
        Integrable.of_finite
      have hlastInt : Integrable (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
          F n p.1 p.2)
          ((pmMeasure G π n i0).compProd (pmStepKernel G π j n)) :=
        Integrable.of_finite
      rw [integral_add hpreInt hlastInt]
      rw [Measure.integral_compProd hpreInt, Measure.integral_compProd hlastInt]
      haveI (h : PMHistory k 𝕊 n) :
          IsProbabilityMeasure (pmStepKernel G π j n h) := inferInstance
      have hprecollapse :
          (∫ h, ∫ _z, (∑ t : Fin n,
              F t (pmHistoryPrefix t t.isLt.le h) (h t))
                ∂pmStepKernel G π j n h ∂pmMeasure G π n i0) =
            ∫ h, ∑ t : Fin n,
              F t (pmHistoryPrefix t t.isLt.le h) (h t)
                ∂pmMeasure G π n i0 := by
        apply integral_congr_ae
        filter_upwards [] with h
        simp
      rw [hprecollapse, ih i0]
      rw [Fin.sum_univ_castSucc]
      dsimp [i0, j]
      congr 1

end
end BanditAlgorithm

open BanditAlgorithm
noncomputable section

/-! Lattimore--Szepesvári, Theorem 37.15, printed pp. 494--495. -/

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k))
    (hS : S.Nonempty) (η B : ℝ) (hη : 0 < η) (hd : 0 < d)
    (hbest : ∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
      ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t))
    (hsolve : ∀ q : Fin k → ℝ, PMSupportedOn S q →
      ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
        PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
        ∀ i : Fin d, pmAlgorithm26Objective G η q p f i ≤ B) :
    ∀ n : ℕ, ∃ π : PMPolicy k 𝕊,
      (⨆ i : Fin n → Fin d, pmRegret G π n i) ≤
        Real.log S.card / η + (n : ℝ) * η * B := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Nonempty (Fin k) := ⟨hS.choose⟩
  intro n
  let Z : (Fin k → ℝ) → ℝ := fun x =>
    ∑ a ∈ S, Real.exp (-η * x a)
  let qOf : (Fin k → ℝ) → Fin k → ℝ := fun x a =>
    if a ∈ S then Real.exp (-η * x a) / Z x else 0
  have hZ (x : Fin k → ℝ) : 0 < Z x := by
    dsimp [Z]
    exact Finset.sum_pos (fun a ha => Real.exp_pos _) hS
  have hqOf (x : Fin k → ℝ) : PMSupportedOn S (qOf x) := by
    constructor
    · constructor
      · intro a
        dsimp [qOf]
        split
        · exact div_nonneg (Real.exp_pos _).le (hZ x).le
        · exact le_rfl
      · dsimp [qOf]
        rw [Finset.sum_ite]
        simp only [Finset.filter_univ_mem, Finset.sum_const_zero, add_zero]
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        change Z x * (Z x)⁻¹ = 1
        exact mul_inv_cancel₀ (hZ x).ne'
    · intro a ha
      simp [qOf, ha]
  choose pOf fOf hpOf hfOf hobjOf using fun x => hsolve (qOf x) (hqOf x)
  let state := pmAlgorithm26State pOf fOf
  let π : PMPolicy k 𝕊 := {
    select := fun t => Kernel.ofFunOfCountable fun h =>
      pmOutcomeMeasure (pOf (state t h))
    markov := by
      intro t
      constructor
      intro h
      exact pmOutcomeMeasure_isProbabilityMeasure _ (hpOf (state t h)).1 }
  have hstepIntegral (t : ℕ) (h : PMHistory k 𝕊 t) (i : Fin d)
      (g : Fin k × 𝕊 → ℝ) :
      ∫ z, g z ∂pmStepKernel G π i t h =
        ∑ a : Fin k, pOf (state t h) a * g (a, G.Φ a i) := by
    rw [pmStepKernel]
    rw [Kernel.map_apply _ (measurable_of_countable _) h]
    rw [MeasureTheory.integral_map
      (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    change ∫ a, g (a, G.Φ a i) ∂pmOutcomeMeasure (pOf (state t h)) = _
    exact integral_pmOutcomeMeasure _ (hpOf (state t h)).1 _
  let yH : PMHistory k 𝕊 n → ℕ → Fin k → ℝ := fun h t b =>
    if ht : t < n then
      let x := state t (pmHistoryPrefix t (Nat.le_of_lt ht) h)
      let obs := h ⟨t, ht⟩
      fOf x obs.1 obs.2 b / pOf x obs.1
    else 0
  have hstate_sum (h : PMHistory k 𝕊 n) (t : ℕ) (ht : t ≤ n) (b : Fin k) :
      state t (pmHistoryPrefix t ht h) b = ∑ s ∈ Finset.range t, yH h s b := by
    induction t with
    | zero => simp [state, pmAlgorithm26State]
    | succ t ih =>
        have htn : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) ht
        rw [Finset.sum_range_succ]
        let hpre := pmHistoryPrefix (t + 1) ht h
        rw [show state (t + 1) hpre b =
            state t (Fin.init hpre) b +
              fOf (state t (Fin.init hpre)) (hpre (Fin.last t)).1
                  (hpre (Fin.last t)).2 b /
                pOf (state t (Fin.init hpre)) (hpre (Fin.last t)).1 by
          simp [state, pmAlgorithm26State]]
        rw [show Fin.init hpre =
            pmHistoryPrefix t (Nat.le_of_lt htn) h by
          funext s
          simp [hpre, pmHistoryPrefix, Fin.init, Fin.castLE]]
        rw [ih (Nat.le_of_lt htn)]
        have hcast : Fin.castLE ht (Fin.last t) = (⟨t, htn⟩ : Fin n) := by
          apply Fin.ext
          rfl
        simp [yH, htn, hpre, pmHistoryPrefix, hcast]
  refine ⟨π, ?_⟩
  apply ciSup_le
  intro i
  obtain ⟨b₀, hb₀S, hb₀⟩ := hbest n i
  let estGap : (t : ℕ) → PMHistory k 𝕊 t → (Fin k × 𝕊) → ℝ :=
    fun t h z =>
      ∑ b : Fin k, qOf (state t h) b *
        (fOf (state t h) z.1 z.2 b / pOf (state t h) z.1 -
          fOf (state t h) z.1 z.2 b₀ / pOf (state t h) z.1)
  let psiTerm : (t : ℕ) → PMHistory k 𝕊 t → (Fin k × 𝕊) → ℝ :=
    fun t h z => pmPsi (qOf (state t h)) (fun b =>
      η * fOf (state t h) z.1 z.2 b / pOf (state t h) z.1)
  have hyH (h : PMHistory k 𝕊 n) (t : Fin n) (b : Fin k) :
      yH h t b =
        fOf (state t (pmHistoryPrefix t t.isLt.le h)) (h t).1 (h t).2 b /
          pOf (state t (pmHistoryPrefix t t.isLt.le h)) (h t).1 := by
    simp [yH, t.isLt]
  have hEW (h : PMHistory k 𝕊 n) :
      (∑ t : Fin n,
          estGap t (pmHistoryPrefix t t.isLt.le h) (h t)) ≤
        Real.log S.card / η + (1 / η) *
          ∑ t : Fin n, psiTerm t (pmHistoryPrefix t t.isLt.le h) (h t) := by
    have hw := expWeights_psi_regret_on_finset S hS n η hη (yH h) b₀ hb₀S
    dsimp only at hw
    have hq (t : Fin n) (a : Fin k) :
        qOf (state t (pmHistoryPrefix t t.isLt.le h)) a =
          if a ∈ S then
            Real.exp (-(η * ∑ s ∈ Finset.range t, yH h s a)) /
              ∑ c ∈ S, Real.exp (-(η * ∑ s ∈ Finset.range t, yH h s c))
          else 0 := by
      simp only [qOf, Z, hstate_sum h]
      ring_nf
    have hlhs :
        (∑ t : Fin n, estGap t (pmHistoryPrefix t t.isLt.le h) (h t)) =
          ∑ t ∈ Finset.range n,
            ∑ a : Fin k,
              (if a ∈ S then
                  Real.exp (-(η * ∑ s ∈ Finset.range t, yH h s a)) /
                    ∑ c ∈ S, Real.exp (-(η * ∑ s ∈ Finset.range t, yH h s c))
                else 0) * (yH h t a - yH h t b₀) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t ht
      simp only [estGap, hq, hyH]
    have hrhs :
        (∑ t ∈ Finset.range n,
            ∑ a : Fin k,
              (if a ∈ S then
                  Real.exp (-(η * ∑ s ∈ Finset.range t, yH h s a)) /
                    ∑ c ∈ S, Real.exp (-(η * ∑ s ∈ Finset.range t, yH h s c))
                else 0) *
                (Real.exp (-η * yH h t a) + η * yH h t a - 1)) =
          ∑ t : Fin n, psiTerm t (pmHistoryPrefix t t.isLt.le h) (h t) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro t ht
      unfold psiTerm pmPsi
      apply Finset.sum_congr rfl
      intro a ha
      rw [hq, hyH]
      ring_nf
    rw [hlhs]
    exact hw.trans_eq (congrArg (fun x => Real.log S.card / η + (1 / η) * x) hrhs)
  let actualGap : (t : ℕ) → PMHistory k 𝕊 t → (Fin k × 𝕊) → ℝ :=
    fun t _h z => if ht : t < n then
      G.L z.1 (i ⟨t, ht⟩) - G.L b₀ (i ⟨t, ht⟩) else 0
  have hest (t : Fin n) (h : PMHistory k 𝕊 t) :
      (∫ z, estGap t h z ∂pmStepKernel G π (i t) t h) =
        ∑ b : Fin k, qOf (state t h) b * (G.L b (i t) - G.L b₀ (i t)) := by
    rw [hstepIntegral]
    exact pmVectorEstimator_importance_weighted_gap G S
      (qOf (state t h)) (pOf (state t h)) (fOf (state t h))
      (hqOf (state t h)) (hpOf (state t h)) (hfOf (state t h))
      (i t) b₀ hb₀S
  have hpsi (t : Fin n) (h : PMHistory k 𝕊 t) :
      (∫ z, psiTerm t h z ∂pmStepKernel G π (i t) t h) =
        ∑ a : Fin k, pOf (state t h) a *
          pmPsi (qOf (state t h)) (fun b =>
            η * fOf (state t h) a (G.Φ a (i t)) b / pOf (state t h) a) := by
    rw [hstepIntegral]
  have hactual (t : Fin n) (h : PMHistory k 𝕊 t) :
      (∫ z, actualGap t h z ∂pmStepKernel G π (i t) t h) =
        ∑ a : Fin k, pOf (state t h) a * (G.L a (i t) - G.L b₀ (i t)) := by
    rw [hstepIntegral]
    simp [actualGap, t.isLt]
  have hround (t : Fin n) (h : PMHistory k 𝕊 t) :
      (∫ z, actualGap t h z ∂pmStepKernel G π (i t) t h) ≤
        (∫ z, estGap t h z ∂pmStepKernel G π (i t) t h) + η * B -
          (1 / η) * (∫ z, psiTerm t h z ∂pmStepKernel G π (i t) t h) := by
    rw [hactual, hest, hpsi]
    let x := state t h
    let q := qOf x
    let p := pOf x
    let f := fOf x
    let P := ∑ a : Fin k, p a *
      pmPsi q (fun b => η * f a (G.Φ a (i t)) b / p a)
    let D := ∑ a : Fin k, (p a - q a) * G.L a (i t)
    have hpSum : ∑ a : Fin k, p a = 1 := (hpOf x).1.2
    have hqSum : ∑ a : Fin k, q a = 1 := (hqOf x).1.2
    have hobj : (1 / η) * D + (1 / η ^ 2) * P ≤ B := by
      simpa [pmAlgorithm26Objective, x, q, p, f, D, P] using hobjOf x (i t)
    have hscaled : D + (1 / η) * P ≤ η * B := by
      have hs := mul_le_mul_of_nonneg_left hobj hη.le
      calc
        D + (1 / η) * P = η * ((1 / η) * D + (1 / η ^ 2) * P) := by
          field_simp [hη.ne']
          <;> ring
        _ ≤ η * B := hs
    have haccount :
        (∑ a : Fin k, p a * (G.L a (i t) - G.L b₀ (i t))) -
            (∑ b : Fin k, q b * (G.L b (i t) - G.L b₀ (i t))) = D := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hpSum, hqSum]
      simp [D]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    dsimp only [x, q, p, f, P, D] at hscaled haccount ⊢
    linarith
  have hEWint :
      (∫ h, ∑ t : Fin n, estGap t (pmHistoryPrefix t t.isLt.le h) (h t)
          ∂pmMeasure G π n i) ≤
        Real.log S.card / η + (1 / η) *
          ∫ h, ∑ t : Fin n, psiTerm t (pmHistoryPrefix t t.isLt.le h) (h t)
            ∂pmMeasure G π n i := by
    have hm := integral_mono (μ := pmMeasure G π n i)
      Integrable.of_finite Integrable.of_finite hEW
    simpa [integral_add, integral_const_mul] using hm
  rw [integral_pm_adapted_sum G π i estGap,
    integral_pm_adapted_sum G π i psiTerm] at hEWint
  have hroundInt (t : Fin n) :
      (∫ h, ∫ z, actualGap t h z ∂pmStepKernel G π (i t) t h
          ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) ≤
        (∫ h, ∫ z, estGap t h z ∂pmStepKernel G π (i t) t h
          ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) + η * B -
        (1 / η) *
          (∫ h, ∫ z, psiTerm t h z ∂pmStepKernel G π (i t) t h
            ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) := by
    have hm := integral_mono
      (μ := pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s)))
      Integrable.of_finite Integrable.of_finite (hround t)
    simpa [integral_add, integral_sub, integral_const_mul] using hm
  have hsumround :
      (∑ t : Fin n,
          ∫ h, ∫ z, actualGap t h z ∂pmStepKernel G π (i t) t h
            ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) ≤
        (∑ t : Fin n,
          ∫ h, ∫ z, estGap t h z ∂pmStepKernel G π (i t) t h
            ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) +
          (n : ℝ) * η * B - (1 / η) *
        (∑ t : Fin n,
          ∫ h, ∫ z, psiTerm t h z ∂pmStepKernel G π (i t) t h
            ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) := by
    calc
      _ ≤ ∑ t : Fin n,
          ((∫ h, ∫ z, estGap t h z ∂pmStepKernel G π (i t) t h
              ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) + η * B -
            (1 / η) *
              (∫ h, ∫ z, psiTerm t h z ∂pmStepKernel G π (i t) t h
                ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s)))) :=
        Finset.sum_le_sum fun t _ => hroundInt t
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.mul_sum]
        ring
  have hactualBound :
      (∑ t : Fin n,
          ∫ h, ∫ z, actualGap t h z ∂pmStepKernel G π (i t) t h
            ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s))) ≤
        Real.log S.card / η + (n : ℝ) * η * B := by
    linarith
  have hactualEq :
      (∫ h, ∑ t : Fin n, (G.L (h t).1 (i t) - G.L b₀ (i t))
          ∂pmMeasure G π n i) =
        ∑ t : Fin n,
          ∫ h, ∫ z, actualGap t h z ∂pmStepKernel G π (i t) t h
            ∂pmMeasure G π t (fun s => i (Fin.castLE t.isLt.le s)) := by
    calc
      _ = ∫ h, ∑ t : Fin n,
          actualGap t (pmHistoryPrefix t t.isLt.le h) (h t)
            ∂pmMeasure G π n i := by
        apply integral_congr_ae
        filter_upwards [] with h
        apply Finset.sum_congr rfl
        intro t ht
        simp [actualGap, t.isLt]
      _ = _ := integral_pm_adapted_sum G π i actualGap
  rw [pmRegret]
  apply ciSup_le
  intro a
  calc
    (∫ h, ∑ t : Fin n, (G.L (h t).1 (i t) - G.L a (i t))
        ∂pmMeasure G π n i) ≤
      ∫ h, ∑ t : Fin n, (G.L (h t).1 (i t) - G.L b₀ (i t))
        ∂pmMeasure G π n i := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro h
      simp only [Finset.sum_sub_distrib]
      linarith [hb₀ a]
    _ = _ := hactualEq
    _ ≤ _ := hactualBound

end
