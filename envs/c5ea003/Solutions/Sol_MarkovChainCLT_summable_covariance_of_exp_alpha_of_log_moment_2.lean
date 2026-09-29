-- Prove2me | solution 2 for MarkovChainCLT.summable_covariance_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T05:39:40.935298+00:00
-- url     : https://prove2.me/submissions/94cb9fa7-c7e8-457d-bc35-01005fb5c7c6

import Definitions.Def_MixingCoefficients
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded
import Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const

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

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace LogCovariance

noncomputable def trunc (T x : ℝ) : ℝ := if |x| ≤ T then x else 0
noncomputable def tail (T x : ℝ) : ℝ := if T < |x| then x ^ 2 else 0

theorem measurable_trunc (T : ℝ) : Measurable (trunc T) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id measurable_const

theorem measurable_tail (T : ℝ) : Measurable (tail T) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) (measurable_id.pow_const 2) measurable_const

theorem trunc_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |trunc T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simpa [trunc, hx] using hx
  · simpa [trunc, hx] using hT

theorem tail_nonneg (T x : ℝ) : 0 ≤ tail T x := by
  unfold tail
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

theorem tail_le_sq (T x : ℝ) : tail T x ≤ x ^ 2 := by
  unfold tail
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

theorem product_tail (T x y : ℝ) :
    |x * y - trunc T x * trunc T y| ≤ tail T x + tail T y := by
  by_cases hx : |x| ≤ T
  · by_cases hy : |y| ≤ T
    · simp [trunc, tail, hx, hy, not_lt.mpr hx, not_lt.mpr hy]
    · have hy' : T < |y| := lt_of_not_ge hy
      have hprod := mul_le_mul_of_nonneg_right (hx.trans hy'.le) (abs_nonneg y)
      simp only [trunc, hx, hy, if_true, if_false, mul_zero, sub_zero, tail,
        not_lt.mpr hx, hy', zero_add, abs_mul]
      nlinarith [sq_abs y]
  · have hx' : T < |x| := lt_of_not_ge hx
    by_cases hy : |y| ≤ T
    · have hprod := mul_le_mul_of_nonneg_left (hy.trans hx'.le) (abs_nonneg x)
      simp only [trunc, hx, hy, if_true, if_false, zero_mul, sub_zero, tail,
        not_lt.mpr hy, hx', add_zero, abs_mul]
      nlinarith [sq_abs x]
    · have hy' : T < |y| := lt_of_not_ge hy
      simp only [trunc, hx, hy, if_false, zero_mul, sub_zero, tail, hx', hy', if_true, abs_mul]
      nlinarith [sq_abs x, sq_abs y, sq_nonneg (|x| - |y|)]

theorem single_tail (T y : ℝ) :
    T * |y - trunc T y| ≤ tail T y := by
  by_cases hy : |y| ≤ T
  · simp [trunc, tail, hy, not_lt.mpr hy]
  · have hy' : T < |y| := lt_of_not_ge hy
    have hprod := mul_le_mul_of_nonneg_right hy'.le (abs_nonneg y)
    simp only [trunc, hy, if_false, sub_zero, tail, hy', if_true]
    nlinarith [sq_abs y]

theorem tail_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (hX2 : MemLp X 2 P) (T : ℝ) :
    Integrable (fun ω => tail T (X ω)) P := by
  refine hX2.integrable_sq.mono' ((measurable_tail T).comp hX).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (tail_nonneg T (X ω))] using tail_le_sq T (X ω)

end LogCovariance

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace LogCovariance

theorem truncation_estimate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hX2 : MemLp X 2 P) (hZ2 : MemLp Z 2 P)
    (T M a : ℝ) (hT : 0 < T)
    (hXM : ∫ ω, tail T (X ω) ∂P = M) (hZM : ∫ ω, tail T (Z ω) ∂P = M)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hc : |cov[fun ω => trunc T (X ω), fun ω => trunc T (Z ω); P]| ≤ 4 * T ^ 2 * a) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * a + 3 * M := by
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
  have hXZ : Integrable (fun ω => X ω * Z ω) P := hX2.integrable_mul hZ2
  have hZi : Integrable Z P := hZ2.integrable (by norm_num)
  have hXt := tail_integrable P X hX hX2 T
  have hZt := tail_integrable P Z hZ hZ2 T
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤ M + M := by
    rw [← integral_sub hXZ hUV]
    calc
      |∫ ω, X ω * Z ω - U ω * V ω ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, tail T (X ω) + tail T (Z ω) ∂P :=
        integral_mono_ae (hXZ.sub hUV).abs (hXt.add hZt)
          (ae_of_all _ fun ω => product_tail T (X ω) (Z ω))
      _ = M + M := by rw [integral_add hXt hZt, hXM, hZM]
  have hsingle : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ M := by
    rw [← integral_sub hZi hVi]
    calc
      T * |∫ ω, Z ω - V ω ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
        mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
      _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
      _ ≤ ∫ ω, tail T (Z ω) ∂P :=
        integral_mono_ae ((hZi.sub hVi).abs.const_mul T) hZt
          (ae_of_all _ fun ω => single_tail T (Z ω))
      _ = M := hZM
  have hEV : T * |∫ ω, V ω ∂P| ≤ M := by
    simpa only [hZ0, zero_sub, abs_neg] using hsingle
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc
      |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P := integral_mono_ae hUi.abs (integrable_const T)
        (ae_of_all _ fun ω => trunc_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * a + M := by
    calc
      |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
        congr 1
        simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * a + M := add_le_add hc hbias
  calc
    |∫ ω, X ω * Z ω ∂P| =
        |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
      rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| :=
      abs_add_le _ _
    _ ≤ (M + M) + (4 * T ^ 2 * a + M) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * a + 3 * M := by ring

end LogCovariance

namespace LogGeometric

theorem exists_rate (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ∃ r : ℝ, 0 < r ∧ Summable (fun n : ℕ => Real.exp (r * (n : ℝ)) ^ 2 * a ^ n) := by
  let b : ℝ := (a + 1) / 2
  have hb0 : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hab : a < b := by dsimp [b]; linarith
  let r : ℝ := -Real.log b / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith [Real.log_neg hb0 hb1]
  have hexp : Real.exp (2 * r) = b⁻¹ := by
    rw [show 2 * r = -Real.log b by dsimp [r]; ring, Real.exp_neg, Real.exp_log hb0]
  have hq0 : 0 ≤ Real.exp (2 * r) * a := mul_nonneg (Real.exp_pos _).le ha0
  have hq1 : Real.exp (2 * r) * a < 1 := by
    rw [hexp, ← div_eq_inv_mul]
    exact (div_lt_one hb0).mpr hab
  refine ⟨r, hr, ?_⟩
  have hs : Summable (fun n : ℕ => (Real.exp (2 * r) * a) ^ n) := summable_geometric_of_norm_lt_one (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)
  convert hs using 1
  funext n
  rw [mul_pow]
  congr 1
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end LogGeometric

open MeasureTheory
open scoped BigOperators

namespace LogTailSeries

theorem sum_exp_square_tails_le (x r : ℝ) (hr : 0 < r) (N : ℕ) :
    (∑ n ∈ Finset.range N, if Real.exp (r * (n : ℝ)) < |x| then x ^ 2 else 0) ≤
      x ^ 2 * (1 + Real.posLog |x| / r) := by
  classical
  let q := Real.posLog |x| / r
  have hq : 0 ≤ q := div_nonneg Real.posLog_nonneg hr.le
  have hsub : (Finset.range N).filter (fun n : ℕ => Real.exp (r * (n : ℝ)) < |x|) ⊆
      Finset.range (Nat.ceil q) := by
    intro n hn
    obtain ⟨_, hn⟩ := Finset.mem_filter.mp hn
    have hlog : r * (n : ℝ) < Real.log |x| := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hn
    have hposlog : Real.log |x| ≤ Real.posLog |x| := le_max_right _ _
    apply Finset.mem_range.mpr
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hr).mpr
    simpa only [mul_comm] using hlog.trans_le hposlog
  calc
    (∑ n ∈ Finset.range N, if Real.exp (r * (n : ℝ)) < |x| then x ^ 2 else 0) =
        ∑ n ∈ (Finset.range N).filter (fun n : ℕ => Real.exp (r * (n : ℝ)) < |x|), x ^ 2 :=
      (Finset.sum_filter _ _).symm
    _ ≤ ∑ _n ∈ Finset.range (Nat.ceil q), x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg x)
    _ = (Nat.ceil q : ℝ) * x ^ 2 := by simp
    _ ≤ (q + 1) * x ^ 2 :=
      mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one hq).le (sq_nonneg x)
    _ = x ^ 2 * (1 + Real.posLog |x| / r) := by dsimp [q]; ring

theorem summable_exp_square_tails {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (hX : Measurable X)
    (h2 : Integrable (fun ω => X ω ^ 2) μ)
    (hlog : Integrable (fun ω => X ω ^ 2 * Real.posLog |X ω|) μ)
    (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℕ =>
      ∫ ω, if Real.exp (r * (n : ℝ)) < |X ω| then X ω ^ 2 else 0 ∂μ) := by
  classical
  let F : ℕ → Ω → ℝ :=
    fun n ω => if Real.exp (r * (n : ℝ)) < |X ω| then X ω ^ 2 else 0
  have hFi (n : ℕ) : Integrable (F n) μ :=
    h2.indicator (measurableSet_lt measurable_const hX.abs)
  have hF0 (n : ℕ) (ω : Ω) : 0 ≤ F n ω := by
    dsimp [F]
    split_ifs
    · exact sq_nonneg _
    · exact le_rfl
  have henv : Integrable (fun ω => X ω ^ 2 * (1 + Real.posLog |X ω| / r)) μ := by
    convert h2.add (hlog.div_const r) using 1
    funext ω
    simp only [Pi.add_apply]
    ring
  apply summable_of_sum_range_le (fun n => integral_nonneg (hF0 n))
  intro N
  calc
    (∑ n ∈ Finset.range N, ∫ ω, F n ω ∂μ) = ∫ ω, ∑ n ∈ Finset.range N, F n ω ∂μ :=
      (integral_finsetSum (Finset.range N) (fun n _ => hFi n)).symm
    _ ≤ ∫ ω, X ω ^ 2 * (1 + Real.posLog |X ω| / r) ∂μ :=
      integral_mono_ae (integrable_finsetSum _ (fun n _ => hFi n)) henv
        (ae_of_all μ fun ω => sum_exp_square_tails_le (X ω) r hr N)

end LogTailSeries

open MeasureTheory ProbabilityTheory MarkovChainCLT

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  obtain ⟨r, hr, hgeom⟩ := LogGeometric.exists_rate a ha0 ha1
  have h02 : MemLp (Y 0) 2 P := (memLp_two_and_logMoment_sub_const P (Y 0) (hY 0) hmom 0).1
  have ht := LogTailSeries.summable_exp_square_tails P (Y 0) (hY 0) h02.integrable_sq hmom r hr
  have hg : Summable (fun n : ℕ => 4 * Real.exp (r * (n : ℝ)) ^ 2 * (max c 0 * a ^ n)) := by
    convert hgeom.mul_left (4 * max c 0) using 1
    funext n
    ring
  have hs : Summable (fun n : ℕ =>
      4 * Real.exp (r * (n : ℝ)) ^ 2 * (max c 0 * a ^ n) +
        3 * ∫ ω, LogCovariance.tail (Real.exp (r * (n : ℝ))) (Y 0 ω) ∂P) :=
    hg.add (ht.mul_left 3)
  apply ((summable_nat_add_iff 1).mpr hs).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs]
  let T := Real.exp (r * ((k + 1 : ℕ) : ℝ))
  let M := ∫ ω, LogCovariance.tail T (Y 0 ω) ∂P
  have hT : 0 < T := Real.exp_pos _
  have hid := CovarianceStationarity.identDistrib_coord P Y hY hstat (k + 1)
  have hk2 : MemLp (Y (k + 1)) 2 P := hid.memLp_iff.mpr h02
  have hkM : ∫ ω, LogCovariance.tail T (Y (k + 1) ω) ∂P = M :=
    (hid.comp (LogCovariance.measurable_tail T)).integral_eq
  have hk0 : ∫ ω, Y (k + 1) ω ∂P = 0 := hid.integral_eq.trans hcent
  have hc := alpha_cov_bounded P Y hY (k + 1) 0
    (fun ω => LogCovariance.trunc T (Y 0 ω))
    (fun ω => LogCovariance.trunc T (Y (k + 1) ω))
    ((LogCovariance.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Iic 0) 0 (by simp)))
    ((LogCovariance.measurable_trunc T).comp
      (CovarianceStationarity.measurable_coord Y (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
    T hT.le (fun ω => LogCovariance.trunc_bound hT.le (Y 0 ω))
    (fun ω => LogCovariance.trunc_bound hT.le (Y (k + 1) ω))
  have hbound := LogCovariance.truncation_estimate P (Y 0) (Y (k + 1)) (hY 0) (hY (k + 1))
    h02 hk2 T M (alphaMixingCoef P Y (k + 1)) hT rfl hkM hk0 hc
  refine hbound.trans ?_
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (hα (k + 1)).trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg ha0 _))

#print axioms solution

