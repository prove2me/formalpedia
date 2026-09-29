-- Prove2me | solution 1 for BanditAlgorithm.pmStochPseudoRegret_pair_tradeoff_of_kl
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T19:42:05.315634+00:00
-- url     : https://prove2.me/submissions/ab950da1-8e4d-4207-b8af-c150eb4d652f

import Definitions.Def_PartialMonitoringStochastic
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality_finite_typeStar
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

private def pmGapSum {k d n : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (u : Fin d → ℝ)
    (a : Fin k) (h : PMHistory k 𝕊 n) : ℝ :=
  ∑ t, (pmExpectedLoss G u (h t).1 - pmExpectedLoss G u a)

private def pmActionSetCountReal {k n : ℕ} {𝕊 : Type*}
    (S : Finset (Fin k)) (h : PMHistory k 𝕊 n) : ℝ :=
  ∑ t, if (h t).1 ∈ S then 1 else 0

private lemma measurable_pmGapSum
    {k d n : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (u : Fin d → ℝ) (a : Fin k) :
    Measurable (pmGapSum G u a : PMHistory k 𝕊 n → ℝ) := by
  unfold pmGapSum
  apply Finset.measurable_sum
  intro t ht
  exact ((measurable_of_countable
    (fun c : Fin k => pmExpectedLoss G u c)).comp
      (measurable_fst.comp (measurable_pi_apply t))).sub measurable_const

private lemma measurable_pmActionSetCountReal
    {k n : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (S : Finset (Fin k)) :
    Measurable (pmActionSetCountReal (n := n) (𝕊 := 𝕊) S) := by
  unfold pmActionSetCountReal
  apply Finset.measurable_sum
  intro t ht
  exact (measurable_of_countable
    (fun c : Fin k => if c ∈ S then (1 : ℝ) else 0)).comp
      (measurable_fst.comp (measurable_pi_apply t))

private lemma integrable_of_finite_domain
    {α : Type*} [Finite α] [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun x : α => ‖f x‖)
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

theorem _root_.solution
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (ua ub : Fin d → ℝ) (hua : ua ∈ stdSimplex ℝ (Fin d))
    (hub : ub ∈ stdSimplex ℝ (Fin d)) (a b : Fin k)
    (N : Finset (Fin k)) (ε C Δ : ℝ)
    (hΔ : 0 < Δ) (hΔε : Δ ≤ ε)
    (haopt : ∀ c : Fin k,
      0 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a)
    (hbopt : ∀ c : Fin k,
      0 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b)
    (houta : ∀ c : Fin k, c ∉ N →
      ε / 2 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a)
    (houtb : ∀ c : Fin k, c ∉ N →
      ε / 2 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b)
    (hinside : ∀ c : Fin k, c ∈ N →
      (pmExpectedLoss G ua c - pmExpectedLoss G ua a) +
        (pmExpectedLoss G ub c - pmExpectedLoss G ub b) = Δ)
    (hKLfin : klDiv (pmStochMeasure G π ua hua n)
      (pmStochMeasure G π ub hub n) ≠ ⊤)
    (hKL : (klDiv (pmStochMeasure G π ua hua n)
      (pmStochMeasure G π ub hub n)).toReal ≤
        C * Δ ^ 2 *
          ∫ h, ∑ t : Fin n,
            (if (h t).1 ∉ N then (1 : ℝ) else 0)
            ∂pmStochMeasure G π ua hua n) :
    ∃ x : ℝ, 0 ≤ x ∧
      ε / 2 * x + (n : ℝ) * Δ / 8 *
          Real.exp (-C * Δ ^ 2 * x) ≤
        pmStochPseudoRegret G π ua hua n a +
          pmStochPseudoRegret G π ub hub n b := by
  classical
  let Bset : Finset (Fin k) := N.filter fun c =>
    Δ / 2 ≤ pmExpectedLoss G ua c - pmExpectedLoss G ua a
  let A : Set (PMHistory k 𝕊 n) :=
    {h | (n : ℝ) / 2 ≤ pmActionSetCountReal Bset h}
  let x : ℝ := ∫ h, pmActionSetCountReal
    (Finset.univ.filter fun c => c ∉ N) h
      ∂pmStochMeasure G π ua hua n
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const (measurable_pmActionSetCountReal Bset)
  have hx : 0 ≤ x := by
    apply integral_nonneg
    intro h
    unfold pmActionSetCountReal
    exact Finset.sum_nonneg fun t ht => by split <;> positivity
  refine ⟨x, hx, ?_⟩
  have huaPoint (h : PMHistory k 𝕊 n) :
      ε / 2 * pmActionSetCountReal
          (Finset.univ.filter fun c => c ∉ N) h +
          (n : ℝ) * Δ / 4 * (if h ∈ A then 1 else 0) ≤
        pmGapSum G ua a h := by
    have hstep (c : Fin k) :
        ε / 2 * (if c ∉ N then (1 : ℝ) else 0) +
            Δ / 2 * (if c ∈ Bset then (1 : ℝ) else 0) ≤
          pmExpectedLoss G ua c - pmExpectedLoss G ua a := by
      by_cases hcN : c ∈ N
      · by_cases hcB : c ∈ Bset
        · have hg := (Finset.mem_filter.mp hcB).2
          simp only [hcN, not_true_eq_false, if_false, hcB, if_true,
            mul_zero, mul_one, zero_add]
          exact hg
        · simp only [hcN, not_true_eq_false, if_false, hcB,
            mul_zero, add_zero]
          exact haopt c
      · have hcB : c ∉ Bset := by simp [Bset, hcN]
        simp only [hcN, not_false_eq_true, if_true, hcB, if_false,
          mul_one, mul_zero, add_zero]
        exact houta c hcN
    have hsum :
        ε / 2 * pmActionSetCountReal
            (Finset.univ.filter fun c => c ∉ N) h +
            Δ / 2 * pmActionSetCountReal Bset h ≤
          pmGapSum G ua a h := by
      unfold pmActionSetCountReal pmGapSum
      calc
        ε / 2 * ∑ t : Fin n,
              (if (h t).1 ∈ Finset.univ.filter (fun c => c ∉ N)
                then (1 : ℝ) else 0) +
            Δ / 2 * ∑ t : Fin n,
              (if (h t).1 ∈ Bset then (1 : ℝ) else 0) =
            ∑ t : Fin n,
              (ε / 2 * (if (h t).1 ∉ N then (1 : ℝ) else 0) +
                Δ / 2 * (if (h t).1 ∈ Bset then (1 : ℝ) else 0)) := by
                  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        _ ≤ ∑ t : Fin n,
              (pmExpectedLoss G ua (h t).1 - pmExpectedLoss G ua a) :=
            Finset.sum_le_sum fun t ht => hstep (h t).1
    by_cases hhA : h ∈ A
    · have hbad : (n : ℝ) / 2 ≤ pmActionSetCountReal Bset h := hhA
      rw [if_pos hhA]
      have hcoef : (n : ℝ) * Δ / 4 ≤
          Δ / 2 * pmActionSetCountReal Bset h := by
        have hmul := mul_le_mul_of_nonneg_left hbad
          (div_nonneg hΔ.le (by positivity : (0 : ℝ) ≤ 2))
        nlinarith
      calc
        ε / 2 * pmActionSetCountReal
              (Finset.univ.filter fun c => c ∉ N) h +
            (n : ℝ) * Δ / 4 * 1 ≤
            ε / 2 * pmActionSetCountReal
              (Finset.univ.filter fun c => c ∉ N) h +
              Δ / 2 * pmActionSetCountReal Bset h := by
                nlinarith [hcoef]
        _ ≤ pmGapSum G ua a h := hsum
    · rw [if_neg hhA, mul_zero, add_zero]
      calc
        ε / 2 * pmActionSetCountReal
            (Finset.univ.filter fun c => c ∉ N) h ≤
            ε / 2 * pmActionSetCountReal
              (Finset.univ.filter fun c => c ∉ N) h +
              Δ / 2 * pmActionSetCountReal Bset h := by
                apply le_add_of_nonneg_right
                exact mul_nonneg (div_nonneg hΔ.le (by positivity))
                  (by unfold pmActionSetCountReal; positivity)
        _ ≤ pmGapSum G ua a h := hsum
  have hubPoint (h : PMHistory k 𝕊 n) :
      (n : ℝ) * Δ / 4 * (if h ∈ Aᶜ then 1 else 0) ≤
        pmGapSum G ub b h := by
    have hnotbad (c : Fin k) (hcB : c ∉ Bset) :
        Δ / 2 ≤ pmExpectedLoss G ub c - pmExpectedLoss G ub b := by
      by_cases hcN : c ∈ N
      · have hnot : ¬ Δ / 2 ≤
            pmExpectedLoss G ua c - pmExpectedLoss G ua a := by
          intro hc
          exact hcB (by simp [Bset, hcN, hc])
        linarith [hinside c hcN]
      · exact le_trans (by linarith) (houtb c hcN)
    have hsum :
        Δ / 2 * ∑ t : Fin n,
            (if (h t).1 ∈ Bset then (0 : ℝ) else 1) ≤
          pmGapSum G ub b h := by
      unfold pmGapSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro t ht
      by_cases hcB : (h t).1 ∈ Bset
      · simp only [hcB, if_true, mul_zero]
        exact hbopt (h t).1
      · simp only [hcB, if_false, mul_one]
        exact hnotbad (h t).1 hcB
    by_cases hhA : h ∈ A
    · have hhAc : h ∉ Aᶜ := by simp [hhA]
      rw [if_neg hhAc, mul_zero]
      unfold pmGapSum
      exact Finset.sum_nonneg fun t ht => hbopt (h t).1
    · have hhAc : h ∈ Aᶜ := by simp [hhA]
      have hbadlt : pmActionSetCountReal Bset h < (n : ℝ) / 2 :=
        lt_of_not_ge hhA
      have hpartition :
          pmActionSetCountReal Bset h +
              ∑ t : Fin n, (if (h t).1 ∈ Bset then (0 : ℝ) else 1) =
            (n : ℝ) := by
        unfold pmActionSetCountReal
        rw [← Finset.sum_add_distrib]
        calc
          ∑ t : Fin n,
              ((if (h t).1 ∈ Bset then (1 : ℝ) else 0) +
                if (h t).1 ∈ Bset then 0 else 1) =
              ∑ _t : Fin n, (1 : ℝ) := by
                apply Finset.sum_congr rfl
                intro t ht
                by_cases hc : (h t).1 ∈ Bset <;> simp [hc]
          _ = (n : ℝ) := by simp
      rw [if_pos hhAc]
      calc
        (n : ℝ) * Δ / 4 * 1 ≤
            Δ / 2 * ∑ t : Fin n,
              (if (h t).1 ∈ Bset then (0 : ℝ) else 1) := by
                nlinarith
        _ ≤ pmGapSum G ub b h := hsum
  let P := pmStochMeasure G π ua hua n
  let Q := pmStochMeasure G π ub hub n
  let fA : PMHistory k 𝕊 n → ℝ := fun h =>
    ε / 2 * pmActionSetCountReal
        (Finset.univ.filter fun c => c ∉ N) h +
      (n : ℝ) * Δ / 4 * (if h ∈ A then 1 else 0)
  let fB : PMHistory k 𝕊 n → ℝ := fun h =>
    (n : ℝ) * Δ / 4 * (if h ∈ Aᶜ then 1 else 0)
  have hIndA : Measurable (fun h : PMHistory k 𝕊 n =>
      if h ∈ A then (1 : ℝ) else 0) := by
    simpa only [Set.indicator, Pi.one_apply] using
      (measurable_const.indicator hA :
        Measurable ((A.indicator fun _ : PMHistory k 𝕊 n => (1 : ℝ))))
  have hIndAc : Measurable (fun h : PMHistory k 𝕊 n =>
      if h ∈ Aᶜ then (1 : ℝ) else 0) := by
    rw [show (fun h : PMHistory k 𝕊 n => if h ∈ Aᶜ then (1 : ℝ) else 0) =
        Aᶜ.indicator (fun _ => (1 : ℝ)) by
      funext h
      simp [Set.indicator]]
    exact measurable_const.indicator hA.compl
  have hfAMeas : Measurable fA :=
    ((measurable_pmActionSetCountReal
      (Finset.univ.filter fun c => c ∉ N)).const_mul _).add
        (hIndA.const_mul _)
  have hfBMeas : Measurable fB := hIndAc.const_mul _
  have hgapAMeas : Measurable (pmGapSum G ua a : PMHistory k 𝕊 n → ℝ) :=
    measurable_pmGapSum G ua a
  have hgapBMeas : Measurable (pmGapSum G ub b : PMHistory k 𝕊 n → ℝ) :=
    measurable_pmGapSum G ub b
  have hfAInt : Integrable fA P := integrable_of_finite_domain hfAMeas
  have hfBInt : Integrable fB Q := integrable_of_finite_domain hfBMeas
  have hgapAInt : Integrable (pmGapSum G ua a) P :=
    integrable_of_finite_domain hgapAMeas
  have hgapBInt : Integrable (pmGapSum G ub b) Q :=
    integrable_of_finite_domain hgapBMeas
  have hintA :
      (∫ h, (if h ∈ A then (1 : ℝ) else 0) ∂P) = P.real A := by
    rw [show (fun h : PMHistory k 𝕊 n => if h ∈ A then (1 : ℝ) else 0) =
        A.indicator (fun _ => (1 : ℝ)) by
      funext h
      simp [Set.indicator]]
    simpa only [Pi.one_apply] using (integral_indicator_one (μ := P) hA)
  have hintAc :
      (∫ h, (if h ∈ Aᶜ then (1 : ℝ) else 0) ∂Q) = Q.real Aᶜ := by
    rw [show (fun h : PMHistory k 𝕊 n => if h ∈ Aᶜ then (1 : ℝ) else 0) =
        Aᶜ.indicator (fun _ => (1 : ℝ)) by
      funext h
      simp [Set.indicator]]
    simpa only [Pi.one_apply] using (integral_indicator_one (μ := Q) hA.compl)
  have hRA : ε / 2 * x + (n : ℝ) * Δ / 4 * P.real A ≤
      pmStochPseudoRegret G π ua hua n a := by
    calc
      ε / 2 * x + (n : ℝ) * Δ / 4 * P.real A = ∫ h, fA h ∂P := by
        rw [show (∫ h, fA h ∂P) =
            ε / 2 * (∫ h, pmActionSetCountReal
              (Finset.univ.filter fun c => c ∉ N) h ∂P) +
              (n : ℝ) * Δ / 4 *
                (∫ h, (if h ∈ A then (1 : ℝ) else 0) ∂P) by
          unfold fA
          rw [integral_add]
          · rw [integral_const_mul, integral_const_mul]
          · exact (integrable_of_finite_domain
              (measurable_pmActionSetCountReal
                (Finset.univ.filter fun c => c ∉ N))).const_mul _
          · exact (integrable_of_finite_domain hIndA).const_mul _]
        rw [hintA]
      _ ≤ ∫ h, pmGapSum G ua a h ∂P :=
        integral_mono hfAInt hgapAInt huaPoint
      _ = pmStochPseudoRegret G π ua hua n a := by
        rfl
  have hRB : (n : ℝ) * Δ / 4 * Q.real Aᶜ ≤
      pmStochPseudoRegret G π ub hub n b := by
    calc
      (n : ℝ) * Δ / 4 * Q.real Aᶜ = ∫ h, fB h ∂Q := by
        unfold fB
        rw [integral_const_mul, hintAc]
      _ ≤ ∫ h, pmGapSum G ub b h ∂Q :=
        integral_mono hfBInt hgapBInt hubPoint
      _ = pmStochPseudoRegret G π ub hub n b := by
        rfl
  have hBH := bretagnolle_huber_inequality_finite_typeStar P Q hA hKLfin
  have hcoef0 : 0 ≤ (n : ℝ) * Δ / 4 := by positivity
  have hBHmul := mul_le_mul_of_nonneg_left hBH hcoef0
  have htest : (n : ℝ) * Δ / 8 *
        Real.exp (-(klDiv P Q).toReal) ≤
      (n : ℝ) * Δ / 4 * (P.real A + Q.real Aᶜ) := by
    nlinarith [hBHmul]
  have hreg : ε / 2 * x + (n : ℝ) * Δ / 8 *
        Real.exp (-(klDiv P Q).toReal) ≤
      pmStochPseudoRegret G π ua hua n a +
        pmStochPseudoRegret G π ub hub n b := by
    nlinarith [hRA, hRB, htest]
  have hKLx : (klDiv P Q).toReal ≤ C * Δ ^ 2 * x := by
    simpa only [P, Q, x, pmActionSetCountReal, Finset.mem_filter,
      Finset.mem_univ, true_and] using hKL
  have hexp : Real.exp (-C * Δ ^ 2 * x) ≤
      Real.exp (-(klDiv P Q).toReal) := by
    apply Real.exp_le_exp.mpr
    linarith
  have htestcoef0 : 0 ≤ (n : ℝ) * Δ / 8 := by positivity
  calc
    ε / 2 * x + (n : ℝ) * Δ / 8 * Real.exp (-C * Δ ^ 2 * x) ≤
        ε / 2 * x + (n : ℝ) * Δ / 8 *
          Real.exp (-(klDiv P Q).toReal) := by
            nlinarith [mul_le_mul_of_nonneg_left hexp htestcoef0]
    _ ≤ pmStochPseudoRegret G π ua hua n a +
          pmStochPseudoRegret G π ub hub n b := hreg

end BanditAlgorithm
