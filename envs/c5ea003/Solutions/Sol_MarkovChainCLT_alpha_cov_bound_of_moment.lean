-- Prove2me | solution 1 for MarkovChainCLT.alpha_cov_bound_of_moment
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:23:35.069198+00:00
-- url     : https://prove2.me/submissions/c21f0eae-d4d4-4824-a4ef-8cdf05013f18

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_MixingCoefficients
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded

open MeasureTheory

namespace CovarianceTail

noncomputable def trunc (T x : ℝ) : ℝ := if |x| ≤ T then x else 0

theorem measurable_trunc (T : ℝ) : Measurable (trunc T) := by
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const)
    measurable_id measurable_const

theorem trunc_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |trunc T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simpa [trunc, hx] using hx
  · simpa [trunc, hx] using hT

theorem trunc_abs_le (T x : ℝ) : |trunc T x| ≤ |x| := by
  by_cases hx : |x| ≤ T
  · simp [trunc, hx]
  · simpa [trunc, hx] using abs_nonneg x

theorem sq_le_rpow_div (δ T a : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (ha : T ≤ a) : a ^ 2 ≤ a ^ (2 + δ) / T ^ δ := by
  have ha0 : 0 < a := hT.trans_le ha
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hT δ)).mpr
  calc
    a ^ 2 * T ^ δ ≤ a ^ 2 * a ^ δ :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT.le ha hδ.le) (sq_nonneg a)
    _ = a ^ (2 + δ) := by rw [Real.rpow_add ha0, Real.rpow_two]

theorem abs_mul_tail_bound (δ T x y : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hout : T < |x| ∨ T < |y|) :
    |x * y| ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
  have hden : 0 ≤ T ^ δ := (Real.rpow_pos_of_pos hT δ).le
  by_cases hxy : |x| ≤ |y|
  · have hyT : T ≤ |y| := by
      rcases hout with hx | hy
      · exact (hx.trans_le hxy).le
      · exact hy.le
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ ≤ |y| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |y| hδ hT hyT
      _ ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hden
        linarith [Real.rpow_nonneg (abs_nonneg x) (2 + δ)]
  · have hyx : |y| ≤ |x| := (lt_of_not_ge hxy).le
    have hxT : T ≤ |x| := by
      rcases hout with hx | hy
      · exact hx.le
      · exact (hy.trans_le hyx).le
    calc
      |x * y| = |x| * |y| := abs_mul x y
      _ ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
      _ ≤ |x| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |x| hδ hT hxT
      _ ≤ (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
        apply div_le_div_of_nonneg_right _ hden
        linarith [Real.rpow_nonneg (abs_nonneg y) (2 + δ)]

theorem product_tail_bound (δ T x y : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    |x * y - trunc T x * trunc T y| ≤
      (|x| ^ (2 + δ) + |y| ^ (2 + δ)) / T ^ δ := by
  by_cases hx : |x| ≤ T
  · by_cases hy : |y| ≤ T
    · simp only [trunc, hx, hy, if_true, sub_self, abs_zero]
      positivity
    · simpa [trunc, hx, hy] using
        abs_mul_tail_bound δ T x y hδ hT (Or.inr (lt_of_not_ge hy))
  · simpa [trunc, hx] using
      abs_mul_tail_bound δ T x y hδ hT (Or.inl (lt_of_not_ge hx))

theorem single_tail_bound (δ T y : ℝ) (hδ : 0 < δ) (hT : 0 < T) :
    T * |y - trunc T y| ≤ |y| ^ (2 + δ) / T ^ δ := by
  by_cases hy : |y| ≤ T
  · simp only [trunc, hy, if_true, sub_self, abs_zero, mul_zero]
    positivity
  · have hTy : T ≤ |y| := (lt_of_not_ge hy).le
    simp only [trunc, hy, if_false, sub_zero]
    calc
      T * |y| ≤ |y| ^ 2 := by nlinarith [abs_nonneg y]
      _ ≤ |y| ^ (2 + δ) / T ^ δ := sq_le_rpow_div δ T |y| hδ hT hTy

theorem abs_mul_le_one_add_rpow (δ x y : ℝ) (hδ : 0 < δ) :
    |x * y| ≤ 1 + |x| ^ (2 + δ) + |y| ^ (2 + δ) := by
  by_cases hx : |x| ≤ 1
  · by_cases hy : |y| ≤ 1
    · have hprod : |x * y| ≤ 1 := by
        rw [abs_mul]
        nlinarith [abs_nonneg x, abs_nonneg y,
          mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 1)]
      linarith [Real.rpow_nonneg (abs_nonneg x) (2 + δ),
        Real.rpow_nonneg (abs_nonneg y) (2 + δ)]
    · have h := abs_mul_tail_bound δ 1 x y hδ (by norm_num)
        (Or.inr (lt_of_not_ge hy))
      simp only [Real.one_rpow, div_one] at h
      linarith
  · have h := abs_mul_tail_bound δ 1 x y hδ (by norm_num)
      (Or.inl (lt_of_not_ge hx))
    simp only [Real.one_rpow, div_one] at h
    linarith

end CovarianceTail

open MeasureTheory ProbabilityTheory MarkovChainCLT

namespace CovarianceStationarity

theorem identDistrib_coord {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hshift : Measurable (fun ω n => Y (n + k) ω) :=
    measurable_pi_lambda _ (fun n => hY (n + k))
  have hfull : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) hshift,
    Measure.map_map (measurable_pi_apply 0) hfull] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

theorem measurable_coord {Ω : Type*} (Y : ℕ → Ω → ℝ) (s : Set ℕ)
    (i : ℕ) (hi : i ∈ s) : Measurable[processSigma Y s] (Y i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

theorem alpha_nonneg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → ℝ) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  apply Real.sSup_nonneg
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact abs_nonneg _

end CovarianceStationarity

open MeasureTheory ProbabilityTheory CovarianceTail
open scoped ProbabilityTheory

namespace CovarianceIntegral

theorem truncation_estimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (δ T M a : ℝ)
    (hδ : 0 < δ) (hT : 0 < T)
    (hXm : Integrable (fun ω => |X ω| ^ (2 + δ)) P)
    (hZm : Integrable (fun ω => |Z ω| ^ (2 + δ)) P)
    (hXM : ∫ ω, |X ω| ^ (2 + δ) ∂P = M)
    (hZM : ∫ ω, |Z ω| ^ (2 + δ) ∂P = M)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hc : |cov[fun ω => trunc T (X ω), fun ω => trunc T (Z ω); P]| ≤ 4 * T ^ 2 * a) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ := by
  let U := fun ω => trunc T (X ω)
  let V := fun ω => trunc T (Z ω)
  have hUm : MemLp U 2 P := MemLp.of_bound
    ((measurable_trunc T).comp hX).aestronglyMeasurable T
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using trunc_bound hT.le (X ω))
  have hVm : MemLp V 2 P := MemLp.of_bound
    ((measurable_trunc T).comp hZ).aestronglyMeasurable T
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using trunc_bound hT.le (Z ω))
  have hUi : Integrable U P := hUm.integrable (by norm_num)
  have hVi : Integrable V P := hVm.integrable (by norm_num)
  have hUV : Integrable (fun ω => U ω * V ω) P := hUm.integrable_mul hVm
  have hXZ : Integrable (fun ω => X ω * Z ω) P := by
    refine (((integrable_const (1 : ℝ)).add hXm).add hZm).mono'
      (hX.mul hZ).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simpa only [Real.norm_eq_abs, Pi.add_apply] using abs_mul_le_one_add_rpow δ (X ω) (Z ω) hδ
  have hZi : Integrable Z P := by
    have hzNorm : Integrable (fun ω => ‖Z ω‖ ^ (1 : ℝ)) P :=
      integrable_norm_rpow_of_le (p := 1) (q := 2 + δ) hZ.aestronglyMeasurable (by norm_num)
        (by linarith) (by linarith)
        (by simpa only [Real.norm_eq_abs] using hZm)
    have hn : Integrable (fun ω => ‖Z ω‖) P := by simpa only [Real.rpow_one] using hzNorm
    exact hn.mono' hZ.aestronglyMeasurable (ae_of_all _ fun _ => le_rfl)
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤
      (M + M) / T ^ δ := by
    rw [← integral_sub hXZ hUV]
    calc
      |∫ ω, X ω * Z ω - U ω * V ω ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|X ω| ^ (2 + δ) + |Z ω| ^ (2 + δ)) / T ^ δ ∂P :=
        integral_mono_ae (hXZ.sub hUV).abs ((hXm.add hZm).div_const (T ^ δ))
          (ae_of_all _ fun ω => product_tail_bound δ T (X ω) (Z ω) hδ hT)
      _ = (M + M) / T ^ δ := by rw [integral_div, integral_add hXm hZm, hXM, hZM]
  have hsingle : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    rw [← integral_sub hZi hVi]
    calc
      T * |∫ ω, Z ω - V ω ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
      _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
      _ ≤ ∫ ω, |Z ω| ^ (2 + δ) / T ^ δ ∂P :=
        integral_mono_ae ((hZi.sub hVi).abs.const_mul T) (hZm.div_const (T ^ δ))
          (ae_of_all _ fun ω => single_tail_bound δ T (Z ω) hδ hT)
      _ = M / T ^ δ := by rw [integral_div, hZM]
  have hEV : T * |∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    simpa only [hZ0, zero_sub, abs_neg] using hsingle
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc
      |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P := integral_mono_ae hUi.abs (integrable_const T)
        (ae_of_all _ fun ω => trunc_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ M / T ^ δ := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * a + M / T ^ δ := by
    calc
      |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
        congr 1
        simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * a + M / T ^ δ := add_le_add hc hbias
  calc
    |∫ ω, X ω * Z ω ∂P| =
        |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
      rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| :=
      abs_add_le _ _
    _ ≤ (M + M) / T ^ δ + (4 * T ^ 2 * a + M / T ^ δ) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * a + 3 * M / T ^ δ := by ring

end CovarianceIntegral

open Filter Topology

namespace CovarianceOptimize

theorem optimize (δ M a v : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) (ha : 0 ≤ a)
    (h : ∀ T : ℝ, 0 < T → v ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ) :
    v ≤ (4 + 3 * M) * a ^ (δ / (2 + δ)) := by
  have hp : 0 < 2 + δ := by linarith
  have hr : 0 < δ / (2 + δ) := div_pos hδ hp
  by_cases ha0 : a = 0
  · subst a
    have hlim : Tendsto (fun T : ℝ => 3 * M / T ^ δ) atTop (𝓝 0) :=
      (tendsto_rpow_atTop hδ).const_div_atTop (3 * M)
    have hv : v ≤ 0 := by
      apply ge_of_tendsto hlim
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simpa only [mul_zero, zero_add] using h T hT
    simpa only [Real.zero_rpow hr.ne', mul_zero] using hv
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let q : ℝ := -1 / (2 + δ)
    let r : ℝ := δ / (2 + δ)
    let T : ℝ := a ^ q
    have hT : 0 < T := Real.rpow_pos_of_pos ha' q
    have hfirst : T ^ 2 * a = a ^ r := by
      calc
        T ^ 2 * a = a ^ (q * 2) * a ^ (1 : ℝ) := by
          rw [Real.rpow_mul ha, Real.rpow_two, Real.rpow_one]
        _ = a ^ (q * 2 + 1) := (Real.rpow_add ha' _ _).symm
        _ = a ^ r := by
          congr 1
          dsimp [q, r]
          field_simp
          ring
    have hsecond : (T ^ δ)⁻¹ = a ^ r := by
      calc
        (T ^ δ)⁻¹ = (a ^ (q * δ))⁻¹ := by rw [Real.rpow_mul ha]
        _ = a ^ (-(q * δ)) := (Real.rpow_neg ha _).symm
        _ = a ^ r := by
          congr 1
          dsimp [q, r]
          ring
    calc
      v ≤ 4 * T ^ 2 * a + 3 * M / T ^ δ := h T hT
      _ = (4 + 3 * M) * a ^ r := by
        rw [div_eq_mul_inv, hsecond]
        nlinarith [hfirst]
      _ = (4 + 3 * M) * a ^ (δ / (2 + δ)) := rfl

end CovarianceOptimize

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (δ : ℝ) (hδ : 0 < δ)
    (hmom : Integrable (fun ω => |Y 0 ω| ^ (2 + δ)) P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |∫ ω, Y 0 ω * Y (k + 1) ω ∂P| ≤ C * alphaMixingCoef P Y (k + 1) ^ (δ / (2 + δ)) := by
  let M := ∫ ω, |Y 0 ω| ^ (2 + δ) ∂P
  have hM : 0 ≤ M := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨4 + 3 * M, by positivity, ?_⟩
  intro k
  apply CovarianceOptimize.optimize δ M (alphaMixingCoef P Y (k + 1))
    (|∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) hδ hM
    (CovarianceStationarity.alpha_nonneg P Y (k + 1))
  intro T hT
  have hid := CovarianceStationarity.identDistrib_coord P Y hY hstat (k + 1)
  have hpow : Measurable (fun x : ℝ => |x| ^ (2 + δ)) := by fun_prop
  have hkm : Integrable (fun ω => |Y (k + 1) ω| ^ (2 + δ)) P :=
    (hid.comp hpow).integrable_iff.mpr hmom
  have hkM : ∫ ω, |Y (k + 1) ω| ^ (2 + δ) ∂P = M := (hid.comp hpow).integral_eq
  have hk0 : ∫ ω, Y (k + 1) ω ∂P = 0 := hid.integral_eq.trans hcent
  apply CovarianceIntegral.truncation_estimate P (Y 0) (Y (k + 1)) (hY 0) (hY (k + 1))
    δ T M (alphaMixingCoef P Y (k + 1)) hδ hT hmom hkm rfl hkM hk0
  exact alpha_cov_bounded P Y hY (k + 1) 0
    (fun ω => CovarianceTail.trunc T (Y 0 ω))
    (fun ω => CovarianceTail.trunc T (Y (k + 1) ω))
    ((CovarianceTail.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Iic 0) 0 (by simp)))
    ((CovarianceTail.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
    T hT.le (fun ω => CovarianceTail.trunc_bound hT.le (Y 0 ω))
    (fun ω => CovarianceTail.trunc_bound hT.le (Y (k + 1) ω))

#print axioms solution
