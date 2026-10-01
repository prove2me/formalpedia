-- Prove2me | solution 1 for MarkovChainCLT.integrable_of_geoDriftCondition
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:29:18.822916+00:00
-- url     : https://prove2.me/submissions/7a57f294-15d0-4e68-b884-8ec6b8708acc

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovDriftMinorization

open MeasureTheory
open scoped ENNReal

namespace DriftTruncation

theorem integrable_of_cutoff_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (V : X → ℝ) (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x)
    (B : ℝ)
    (hint : ∀ n : ℕ, Integrable (fun x => if V x ≤ (n : ℝ) then V x else 0) μ)
    (hbound : ∀ n : ℕ, (∫ x, if V x ≤ (n : ℝ) then V x else 0 ∂μ) ≤ B) :
    Integrable V μ := by
  let F : ℕ → X → ℝ := fun n x => if V x ≤ (n : ℝ) then V x else 0
  have hF0 (n : ℕ) (x : X) : 0 ≤ F n x := by
    dsimp [F]
    split_ifs
    · exact hV0 x
    · exact le_rfl
  have hFle (n : ℕ) (x : X) : F n x ≤ V x := by
    dsimp [F]
    split_ifs
    · exact le_rfl
    · exact hV0 x
  have hFm (n : ℕ) : Measurable (F n) :=
    Measurable.ite (measurableSet_le hV measurable_const) hV measurable_const
  have hmono : Monotone (fun n : ℕ => fun x => ENNReal.ofReal (F n x)) := by
    intro n m hnm x
    by_cases hx : V x ≤ (n : ℝ)
    · have hxm : V x ≤ (m : ℝ) := hx.trans (Nat.cast_le.mpr hnm)
      simp only [F, hx, hxm, if_true, le_refl]
    · simp only [F, hx, if_false, ENNReal.ofReal_zero]
      exact bot_le
  have hsup (x : X) : (⨆ n : ℕ, ENNReal.ofReal (F n x)) = ENNReal.ofReal (V x) := by
    apply le_antisymm
    · exact iSup_le (fun n => ENNReal.ofReal_le_ofReal (hFle n x))
    · obtain ⟨n, hn⟩ := exists_nat_ge (V x)
      exact le_iSup_of_le n (by simp only [F, hn, if_true, le_refl])
  have hlin (n : ℕ) : (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all μ (hF0 n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hfin : (∫⁻ x, ENNReal.ofReal (V x) ∂μ) < ∞ := by
    calc
      (∫⁻ x, ENNReal.ofReal (V x) ∂μ) = ∫⁻ x, ⨆ n : ℕ, ENNReal.ofReal (F n x) ∂μ := by
        apply lintegral_congr
        intro x
        exact (hsup x).symm
      _ = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (F n x) ∂μ :=
        lintegral_iSup (fun n => (hFm n).ennreal_ofReal) hmono
      _ ≤ ENNReal.ofReal B := iSup_le hlin
      _ < ∞ := ENNReal.ofReal_lt_top
  exact ⟨hV.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all μ hV0)).mpr hfin⟩

end DriftTruncation

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace DriftBound

theorem cutoff_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (V : X → ℝ)
    (hV : Measurable V) (hV0 : ∀ x, 0 ≤ V x) (n : ℕ) :
    Integrable (fun x => if V x ≤ (n : ℝ) then V x else 0) μ := by
  refine (integrable_const (n : ℝ)).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (Measurable.ite (measurableSet_le hV measurable_const) hV measurable_const).aestronglyMeasurable
  · by_cases hx : V x ≤ (n : ℝ)
    · simpa only [if_pos hx, Real.norm_eq_abs, abs_of_nonneg (hV0 x)] using hx
    · simp only [if_neg hx, norm_zero]
      positivity

theorem cutoff_integral_bound {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : Kernel.Invariant P π) (V : X → ℝ) (hV : Measurable V)
    (hV0 : ∀ x, 0 ≤ V x) (d B : ℝ) (hd : 0 < d) (hB : 0 ≤ B)
    (hVi : ∀ x, Integrable V (P x))
    (hdrift : ∀ x, (∫ y, V y ∂P x) - V x ≤ -d * V x + B) (n : ℕ) :
    (∫ x, (if V x ≤ (n : ℝ) then V x else 0) ∂π) ≤ B / d := by
  let F : X → ℝ := fun x => min (V x) (n : ℝ)
  have hF0 : ∀ x, 0 ≤ F x := fun x => le_min (hV0 x) (by positivity)
  have hFn : ∀ x, F x ≤ (n : ℝ) := fun x => min_le_right _ _
  have hFm : Measurable F := hV.min measurable_const
  have hFi : ∀ (μ : Measure X) [IsProbabilityMeasure μ], Integrable F μ := by
    intro μ hμ
    refine (integrable_const (n : ℝ)).mono' hFm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 x)] using hFn x
  have hPF0 : ∀ x, 0 ≤ ∫ y, F y ∂P x := fun x => integral_nonneg hF0
  have hPFn : ∀ x, (∫ y, F y ∂P x) ≤ (n : ℝ) := by
    intro x
    calc
      (∫ y, F y ∂P x) ≤ ∫ _ : X, (n : ℝ) ∂P x :=
        integral_mono_ae (hFi (P x)) (integrable_const _) (ae_of_all _ hFn)
      _ = n := by simp
  have hPFi : Integrable (fun x => ∫ y, F y ∂P x) π := by
    refine (integrable_const (n : ℝ)).mono'
      hFm.stronglyMeasurable.integral_kernel.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hPF0 x)] using hPFn x
  have hcomp : (P ∘ₖ Kernel.const Unit π) () = π := by
    change π.bind P = π
    exact hP
  have hcompFi : Integrable F ((P ∘ₖ Kernel.const Unit π) ()) := by
    rw [hcomp]
    exact hFi π
  have hstationary : (∫ x, ∫ y, F y ∂P x ∂π) = ∫ x, F x ∂π := by
    simpa only [hcomp, Kernel.const_apply] using (Kernel.integral_comp hcompFi).symm
  have hpoint : ∀ x, d * (if V x ≤ (n : ℝ) then V x else 0) ≤
      F x - (∫ y, F y ∂P x) + B := by
    intro x
    by_cases hx : V x ≤ (n : ℝ)
    · have hFV : (∫ y, F y ∂P x) ≤ ∫ y, V y ∂P x :=
        integral_mono_ae (hFi (P x)) (hVi x) (ae_of_all _ fun y => min_le_left _ _)
      have hxF : F x = V x := min_eq_left hx
      rw [if_pos hx, hxF]
      linarith [hdrift x]
    · have hxF : F x = n := min_eq_right (le_of_not_ge hx)
      rw [if_neg hx, mul_zero, hxF]
      linarith [hPFn x]
  have hdiffi : Integrable (fun x => F x - (∫ y, F y ∂P x)) π := (hFi π).sub hPFi
  have hbound := integral_mono_ae
    ((cutoff_integrable π V hV hV0 n).const_mul d)
    (hdiffi.add (integrable_const B)) (ae_of_all _ hpoint)
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add hdiffi (integrable_const B),
    integral_sub (hFi π) hPFi, hstationary] at hbound
  simp only [sub_self, zero_add, integral_const, probReal_univ, smul_eq_mul,
    one_mul] at hbound
  exact (le_div_iff₀ hd).mpr (by nlinarith)

end DriftBound

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π)
    (V : X → ℝ) (hV : Measurable V) (hV1 : ∀ x, 1 ≤ V x)
    (C : Set X) (hC : MeasurableSet C) (hsmall : IsSmallSet P C)
    (d b : ℝ) (hd : 0 < d) (hdrift : GeoDriftCondition P V d b C) :
    Integrable V π := by
  have hV0 : ∀ x, 0 ≤ V x := fun x => le_trans zero_le_one (hV1 x)
  apply DriftTruncation.integrable_of_cutoff_bounds π V hV hV0 (max b 0 / d)
    (DriftBound.cutoff_integrable π V hV hV0)
  intro n
  apply DriftBound.cutoff_integral_bound P π hP.1 V hV hV0 d (max b 0) hd
    (le_max_right b 0) hdrift.1
  intro x
  have hb : b * C.indicator (fun _ => (1 : ℝ)) x ≤ max b 0 := by
    by_cases hx : x ∈ C
    · simpa [hx] using le_max_left b (0 : ℝ)
    · simpa [hx] using le_max_right b (0 : ℝ)
  linarith [hdrift.2 x]

#print axioms solution
