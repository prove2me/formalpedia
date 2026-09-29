-- Prove2me | solution 1 for MarkovChainCLT.summable_covariance_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T05:37:30.587753+00:00
-- url     : https://prove2.me/submissions/b4ddeb01-53ae-430c-a166-0197d09d3998

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ProbabilityTheory ENNReal

namespace ExpAlphaLogMomentAux

/-- Truncation of a real number at level `T`. -/
noncomputable def truncAt (T x : ℝ) : ℝ := if |x| ≤ T then x else 0

/-- The squared tail `x² 1{|x| > T}`. -/
noncomputable def tailSq (T x : ℝ) : ℝ := if |x| ≤ T then 0 else x ^ 2

theorem measurable_truncAt (T : ℝ) : Measurable (truncAt T) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_id
    measurable_const

theorem measurable_tailSq (T : ℝ) : Measurable (tailSq T) :=
  Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_const
    (measurable_id.pow_const 2)

theorem truncAt_bound {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |truncAt T x| ≤ T := by
  by_cases hx : |x| ≤ T
  · simp [truncAt, hx]
  · simpa [truncAt, hx] using hT

theorem tailSq_nonneg (T x : ℝ) : 0 ≤ tailSq T x := by
  by_cases hx : |x| ≤ T <;> simp [tailSq, hx, sq_nonneg]

theorem tailSq_le_sq (T x : ℝ) : tailSq T x ≤ x ^ 2 := by
  by_cases hx : |x| ≤ T <;> simp [tailSq, hx, sq_nonneg]

/-- Pointwise control of the truncation error in a product. -/
theorem abs_mul_sub_truncAt_mul_le (T x z : ℝ) :
    |x * z - truncAt T x * truncAt T z| ≤ tailSq T x + tailSq T z := by
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  by_cases hx : |x| ≤ T
  · by_cases hz : |z| ≤ T
    · simp [truncAt, tailSq, hx, hz]
    · have hzT : T < |z| := lt_of_not_ge hz
      have h1 : |x * z| ≤ z ^ 2 := by
        rw [abs_mul]
        have : |x| * |z| ≤ |z| * |z| :=
          mul_le_mul_of_nonneg_right (hx.trans hzT.le) (abs_nonneg z)
        calc |x| * |z| ≤ |z| * |z| := this
          _ = z ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
      simpa [truncAt, tailSq, hx, hz] using h1.trans (by linarith)
  · have hxT : T < |x| := lt_of_not_ge hx
    by_cases hz : |z| ≤ T
    · have h1 : |x * z| ≤ x ^ 2 := by
        rw [abs_mul]
        have : |x| * |z| ≤ |x| * |x| :=
          mul_le_mul_of_nonneg_left (hz.trans hxT.le) (abs_nonneg x)
        calc |x| * |z| ≤ |x| * |x| := this
          _ = x ^ 2 := by rw [← abs_mul, ← sq, abs_sq]
      simpa [truncAt, tailSq, hx, hz] using h1.trans (by linarith)
    · have h1 : |x * z| ≤ x ^ 2 + z ^ 2 := by
        rw [abs_mul]
        nlinarith [abs_nonneg x, abs_nonneg z, sq_nonneg (|x| - |z|), sq_abs x, sq_abs z]
      simpa [truncAt, tailSq, hx, hz] using h1

/-- Pointwise control of the truncation error in a single variable. -/
theorem mul_abs_sub_truncAt_le (T x : ℝ) :
    T * |x - truncAt T x| ≤ tailSq T x := by
  by_cases hx : |x| ≤ T
  · simp [truncAt, tailSq, hx]
  · have hxT : T < |x| := lt_of_not_ge hx
    have : T * |x| ≤ |x| * |x| := mul_le_mul_of_nonneg_right hxT.le (abs_nonneg x)
    simpa [truncAt, tailSq, hx, ← sq, sq_abs] using this

section Estimate

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The key per-lag estimate: the expectation of a product is controlled by the
mixing coefficient at the truncation level plus the squared tails. -/
theorem abs_integral_mul_le_of_cov_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (T t c : ℝ) (hT : 0 < T)
    (hX2 : MemLp X 2 P) (hZ2 : MemLp Z 2 P)
    (htX : ∫ ω, tailSq T (X ω) ∂P = t) (htZ : ∫ ω, tailSq T (Z ω) ∂P = t)
    (hZ0 : ∫ ω, Z ω ∂P = 0)
    (hcov : |cov[fun ω => truncAt T (X ω), fun ω => truncAt T (Z ω); P]| ≤ 4 * T ^ 2 * c) :
    |∫ ω, X ω * Z ω ∂P| ≤ 4 * T ^ 2 * c + 3 * t := by
  set U : Ω → ℝ := fun ω => truncAt T (X ω) with hU
  set V : Ω → ℝ := fun ω => truncAt T (Z ω) with hV
  have hUmeas : Measurable U := (measurable_truncAt T).comp hX
  have hVmeas : Measurable V := (measurable_truncAt T).comp hZ
  have hUm : MemLp U 2 P :=
    MemLp.of_bound hUmeas.aestronglyMeasurable T
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using truncAt_bound hT.le (X ω))
  have hVm : MemLp V 2 P :=
    MemLp.of_bound hVmeas.aestronglyMeasurable T
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using truncAt_bound hT.le (Z ω))
  have hUi : Integrable U P := hUm.integrable (by norm_num)
  have hVi : Integrable V P := hVm.integrable (by norm_num)
  have hUV : Integrable (fun ω => U ω * V ω) P := hUm.integrable_mul hVm
  have hXZ : Integrable (fun ω => X ω * Z ω) P := hX2.integrable_mul hZ2
  have hZi : Integrable Z P := hZ2.integrable (by norm_num)
  have hXsq : Integrable (fun ω => X ω ^ 2) P := by
    simpa using hX2.integrable_sq
  have hZsq : Integrable (fun ω => Z ω ^ 2) P := by
    simpa using hZ2.integrable_sq
  have htailX : Integrable (fun ω => tailSq T (X ω)) P := by
    refine hXsq.mono' ((measurable_tailSq T).comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
    exact tailSq_le_sq _ _
  have htailZ : Integrable (fun ω => tailSq T (Z ω)) P := by
    refine hZsq.mono' ((measurable_tailSq T).comp hZ).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
    exact tailSq_le_sq _ _
  -- the product error
  have hproduct : |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| ≤ t + t := by
    rw [← integral_sub hXZ hUV]
    calc |∫ ω, (X ω * Z ω - U ω * V ω) ∂P| ≤ ∫ ω, |X ω * Z ω - U ω * V ω| ∂P :=
          abs_integral_le_integral_abs
      _ ≤ ∫ ω, (tailSq T (X ω) + tailSq T (Z ω)) ∂P :=
          integral_mono_ae (hXZ.sub hUV).abs (htailX.add htailZ)
            (ae_of_all _ fun ω => abs_mul_sub_truncAt_mul_le T (X ω) (Z ω))
      _ = t + t := by rw [integral_add htailX htailZ, htX, htZ]
  -- the mean of the truncation
  have hEV : T * |∫ ω, V ω ∂P| ≤ t := by
    have h1 : T * |(∫ ω, Z ω ∂P) - ∫ ω, V ω ∂P| ≤ t := by
      rw [← integral_sub hZi hVi]
      calc T * |∫ ω, (Z ω - V ω) ∂P| ≤ T * ∫ ω, |Z ω - V ω| ∂P :=
            mul_le_mul_of_nonneg_left abs_integral_le_integral_abs hT.le
        _ = ∫ ω, T * |Z ω - V ω| ∂P := (integral_const_mul T _).symm
        _ ≤ ∫ ω, tailSq T (Z ω) ∂P :=
            integral_mono_ae ((hZi.sub hVi).abs.const_mul T) htailZ
              (ae_of_all _ fun ω => mul_abs_sub_truncAt_le T (Z ω))
        _ = t := htZ
    simpa only [hZ0, zero_sub, abs_neg] using h1
  have hEU : |∫ ω, U ω ∂P| ≤ T := by
    calc |∫ ω, U ω ∂P| ≤ ∫ ω, |U ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _ : Ω, T ∂P :=
          integral_mono_ae hUi.abs (integrable_const T)
            (ae_of_all _ fun ω => truncAt_bound hT.le (X ω))
      _ = T := by simp
  have hbias : |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| ≤ t := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hEU (abs_nonneg _)).trans hEV
  have hcId := covariance_eq_sub hUm hVm
  have htrunc : |∫ ω, U ω * V ω ∂P| ≤ 4 * T ^ 2 * c + t := by
    calc |∫ ω, U ω * V ω ∂P| = |cov[U, V; P] + (∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := by
          congr 1
          simpa only [Pi.mul_apply] using (eq_add_of_sub_eq hcId.symm)
      _ ≤ |cov[U, V; P]| + |(∫ ω, U ω ∂P) * ∫ ω, V ω ∂P| := abs_add_le _ _
      _ ≤ 4 * T ^ 2 * c + t := add_le_add hcov hbias
  calc |∫ ω, X ω * Z ω ∂P|
      = |((∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P) + ∫ ω, U ω * V ω ∂P| := by
        rw [sub_add_cancel]
    _ ≤ |(∫ ω, X ω * Z ω ∂P) - ∫ ω, U ω * V ω ∂P| + |∫ ω, U ω * V ω ∂P| := abs_add_le _ _
    _ ≤ (t + t) + (4 * T ^ 2 * c + t) := add_le_add hproduct htrunc
    _ = 4 * T ^ 2 * c + 3 * t := by ring

end Estimate

/-- Pointwise: the number of scales `R^k` below `|x|` is controlled by `log⁺|x| / log R`. -/
theorem sum_tailSq_pow_le {R : ℝ} (hR : 1 < R) (x : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range N, tailSq (R ^ k) x ≤ x ^ 2 + x ^ 2 * Real.posLog |x| / Real.log R := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  set L : ℝ := Real.posLog |x| / Real.log R with hL
  have hL0 : 0 ≤ L := div_nonneg (Real.posLog_nonneg) hlogR.le
  have hsub : (Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k) ⊆
      Finset.range (⌊L⌋₊ + 1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, not_le] at hk
    obtain ⟨-, hk2⟩ := hk
    have hxpos : (0 : ℝ) < |x| := lt_of_le_of_lt (by positivity) hk2
    have hlog : (k : ℝ) * Real.log R < Real.log |x| := by
      have := Real.log_lt_log (by positivity) hk2
      rwa [Real.log_pow] at this
    have hle : Real.log |x| ≤ Real.posLog |x| := by
      rw [Real.posLog_def]; exact le_max_right _ _
    have : (k : ℝ) < L := by
      rw [hL, lt_div_iff₀ hlogR]
      linarith
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor this.le))
  have hcard : (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ) ≤ L + 1 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have : (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ) ≤ (⌊L⌋₊ + 1 : ℕ) := by
      exact_mod_cast h1
    refine this.trans ?_
    push_cast
    have := Nat.floor_le hL0
    linarith
  have hsum : ∑ k ∈ Finset.range N, tailSq (R ^ k) x
      = x ^ 2 * (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ) := by
    simp only [tailSq]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_zero, zero_add, nsmul_eq_mul,
      mul_comm]
  rw [hsum]
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  calc x ^ 2 * (((Finset.range N).filter (fun k => ¬ |x| ≤ R ^ k)).card : ℝ)
      ≤ x ^ 2 * (L + 1) := mul_le_mul_of_nonneg_left hcard hx2
    _ = x ^ 2 + x ^ 2 * Real.posLog |x| / Real.log R := by rw [hL]; ring

section LogMoment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An `x² log⁺|x|` moment forces square integrability. -/
theorem memLp_two_of_logMoment (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hmom : Integrable (fun ω => X ω ^ 2 * Real.posLog |X ω|) P) :
    MemLp X 2 P := by
  refine (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).2 ?_
  refine ((integrable_const (Real.exp 2)).add hmom).mono'
    (hX.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hpos : 0 ≤ X ω ^ 2 * Real.posLog |X ω| :=
    mul_nonneg (sq_nonneg _) Real.posLog_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hexp : Real.exp 1 ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  by_cases hx : |X ω| ≤ Real.exp 1
  · have : X ω ^ 2 ≤ Real.exp 2 := by
      have h1 : |X ω| ^ 2 ≤ Real.exp 1 ^ 2 := by
        have := mul_self_le_mul_self (abs_nonneg (X ω)) hx
        nlinarith
      calc X ω ^ 2 = |X ω| ^ 2 := (sq_abs _).symm
        _ ≤ Real.exp 1 ^ 2 := h1
        _ = Real.exp 2 := hexp
    simp only [Pi.add_apply]
    linarith
  · have hxe : Real.exp 1 < |X ω| := lt_of_not_ge hx
    have h1 : (1 : ℝ) ≤ Real.posLog |X ω| := by
      have hge : (1 : ℝ) ≤ Real.log |X ω| := by
        have h := Real.log_lt_log (Real.exp_pos 1) hxe
        rw [Real.log_exp] at h
        exact h.le
      rw [Real.posLog_def]
      exact le_max_of_le_right hge
    have h2 : X ω ^ 2 ≤ X ω ^ 2 * Real.posLog |X ω| := by
      nlinarith [sq_nonneg (X ω)]
    simp only [Pi.add_apply]
    have : (0 : ℝ) ≤ Real.exp 2 := (Real.exp_pos 2).le
    linarith

/-- The squared tails at the geometric scales `R^k` are summable. -/
theorem summable_integral_tailSq (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hmom : Integrable (fun ω => X ω ^ 2 * Real.posLog |X ω|) P)
    {R : ℝ} (hR : 1 < R) :
    Summable (fun k : ℕ => ∫ ω, tailSq (R ^ k) (X ω) ∂P) := by
  have hX2 : MemLp X 2 P := memLp_two_of_logMoment P X hX hmom
  have hXsq : Integrable (fun ω => X ω ^ 2) P := hX2.integrable_sq
  have hint : ∀ k : ℕ, Integrable (fun ω => tailSq (R ^ k) (X ω)) P := by
    intro k
    refine hXsq.mono' ((measurable_tailSq _).comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
    exact tailSq_le_sq _ _
  refine summable_of_sum_range_le
    (fun k => integral_nonneg fun ω => tailSq_nonneg _ _)
    (c := (∫ ω, X ω ^ 2 ∂P) + (∫ ω, X ω ^ 2 * Real.posLog |X ω| ∂P) / Real.log R) ?_
  intro N
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range N, tailSq (R ^ k) (X ω)) P :=
    integrable_finsetSum _ fun k _ => hint k
  calc ∑ k ∈ Finset.range N, ∫ ω, tailSq (R ^ k) (X ω) ∂P
      = ∫ ω, ∑ k ∈ Finset.range N, tailSq (R ^ k) (X ω) ∂P :=
        (integral_finsetSum _ fun k _ => hint k).symm
    _ ≤ ∫ ω, (X ω ^ 2 + X ω ^ 2 * Real.posLog |X ω| / Real.log R) ∂P :=
        integral_mono hsumint (hXsq.add (hmom.div_const _))
          (fun ω => sum_tailSq_pow_le hR (X ω) N)
    _ = (∫ ω, X ω ^ 2 ∂P) + (∫ ω, X ω ^ 2 * Real.posLog |X ω| ∂P) / Real.log R := by
        rw [integral_add hXsq (hmom.div_const _), integral_div]

end LogMoment

section Main

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Under strict stationarity every coordinate has the law of the first one. -/
theorem identDistrib_coord (P : Measure Ω) (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hs : IsStrictlyStationary P Y) (k : ℕ) : IdentDistrib (Y k) (Y 0) P P := by
  refine ⟨(hY k).aemeasurable, (hY 0).aemeasurable, ?_⟩
  have hshift : Measurable (fun ω n => Y (n + k) ω) :=
    measurable_pi_lambda _ (fun n => hY (n + k))
  have hfull : Measurable (fun ω n => Y n ω) := measurable_pi_lambda _ hY
  have hm := congrArg (Measure.map (fun z : ℕ → ℝ => z 0)) (hs k)
  rw [Measure.map_map (measurable_pi_apply 0) hshift,
    Measure.map_map (measurable_pi_apply 0) hfull] at hm
  simpa only [Function.comp_def, Nat.zero_add] using hm

omit [MeasurableSpace Ω] in
/-- A coordinate is measurable for the process σ-algebra of any index set containing it. -/
theorem measurable_coord {E : Type*} [MeasurableSpace E] (Y : ℕ → Ω → E) (s : Set ℕ)
    (i : ℕ) (hi : i ∈ s) : Measurable[processSigma Y s] (Y i) := by
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)

/-- The strong mixing coefficient is nonnegative. -/
theorem alphaMixingCoef_nonneg {E : Type*} [MeasurableSpace E] (P : Measure Ω)
    (Y : ℕ → Ω → E) (n : ℕ) : 0 ≤ alphaMixingCoef P Y n := by
  apply Real.sSup_nonneg
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  exact abs_nonneg _


/-- The main estimate, with the bounded covariance inequality supplied as `hcovb`. -/
theorem summable_covariance_of_exp_alpha_of_log_moment_aux
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hal : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (hcovb : ∀ (n k : ℕ) (U V : Ω → ℝ),
      Measurable[processSigma Y (Set.Iic k)] U →
      Measurable[processSigma Y (Set.Ici (k + n))] V →
      ∀ M : ℝ, 0 ≤ M → (∀ ω, |U ω| ≤ M) → (∀ ω, |V ω| ≤ M) →
        |cov[U, V; P]| ≤ 4 * M ^ 2 * alphaMixingCoef P Y n) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  have h1a : (0 : ℝ) < 1 + a := by linarith
  set R : ℝ := Real.sqrt (2 / (1 + a)) with hRdef
  have hR2 : R ^ 2 = 2 / (1 + a) := Real.sq_sqrt (by positivity)
  have hR1 : 1 < R := by
    have h2 : (1 : ℝ) < 2 / (1 + a) := by rw [lt_div_iff₀ h1a]; linarith
    nlinarith [Real.sqrt_nonneg (2 / (1 + a)), hR2]
  have hR0 : 0 < R := lt_trans zero_lt_one hR1
  set q : ℝ := a * R ^ 2 with hqdef
  have hq0 : 0 ≤ q := mul_nonneg ha0 (sq_nonneg R)
  have hq1 : q < 1 := by
    rw [hqdef, hR2, mul_div_assoc']
    rw [div_lt_one h1a]
    linarith
  have hX2 : MemLp (Y 0) 2 P := memLp_two_of_logMoment P (Y 0) (hY 0) hmom
  have hXsq : Integrable (fun ω => Y 0 ω ^ 2) P := hX2.integrable_sq
  set t : ℕ → ℝ := fun k => ∫ ω, tailSq (R ^ k) (Y 0 ω) ∂P with htdef
  have htail : Summable t := summable_integral_tailSq P (Y 0) (hY 0) hmom hR1
  -- the majorant
  have hgeo : Summable (fun k : ℕ => 4 * c * a * q ^ k) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hS1 : Summable (fun k : ℕ => 4 * (R ^ k) ^ 2 * alphaMixingCoef P Y (k + 1)) := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hgeo
    · exact mul_nonneg (by positivity) (alphaMixingCoef_nonneg P Y (k + 1))
    · have h1 : alphaMixingCoef P Y (k + 1) ≤ c * a ^ (k + 1) := hal (k + 1)
      have h2 : (0 : ℝ) ≤ 4 * (R ^ k) ^ 2 := by positivity
      calc 4 * (R ^ k) ^ 2 * alphaMixingCoef P Y (k + 1)
          ≤ 4 * (R ^ k) ^ 2 * (c * a ^ (k + 1)) := mul_le_mul_of_nonneg_left h1 h2
        _ = 4 * c * a * (a * R ^ 2) ^ k := by
            rw [mul_pow, ← pow_mul, ← pow_mul]
            ring_nf
        _ = 4 * c * a * q ^ k := by rw [hqdef]
  have hmaj : Summable (fun k : ℕ =>
      4 * (R ^ k) ^ 2 * alphaMixingCoef P Y (k + 1) + 3 * t k) := hS1.add (htail.mul_left 3)
  refine hmaj.of_norm_bounded ?_
  intro k
  -- the per-lag estimate
  have hid : IdentDistrib (Y (k + 1)) (Y 0) P P := identDistrib_coord P Y hY hstat (k + 1)
  have hZsq : Integrable (fun ω => Y (k + 1) ω ^ 2) P :=
    (hid.comp (measurable_id.pow_const 2)).integrable_iff.mpr hXsq
  have hZ2 : MemLp (Y (k + 1)) 2 P :=
    (memLp_two_iff_integrable_sq (hY (k + 1)).aestronglyMeasurable).2 hZsq
  have hZ0 : ∫ ω, Y (k + 1) ω ∂P = 0 := hid.integral_eq.trans hcent
  have htZ : ∫ ω, tailSq (R ^ k) (Y (k + 1) ω) ∂P = t k :=
    (hid.comp (measurable_tailSq (R ^ k))).integral_eq
  have hTpos : (0 : ℝ) < R ^ k := by positivity
  have hcov : |cov[fun ω => truncAt (R ^ k) (Y 0 ω),
      fun ω => truncAt (R ^ k) (Y (k + 1) ω); P]|
      ≤ 4 * (R ^ k) ^ 2 * alphaMixingCoef P Y (k + 1) := by
    refine hcovb (k + 1) 0 _ _
      ((measurable_truncAt _).comp (measurable_coord Y (Set.Iic 0) 0 (by simp)))
      ((measurable_truncAt _).comp
        (measurable_coord Y (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
      (R ^ k) hTpos.le (fun ω => truncAt_bound hTpos.le _)
      (fun ω => truncAt_bound hTpos.le _)
  have := abs_integral_mul_le_of_cov_bound P (Y 0) (Y (k + 1)) (hY 0) (hY (k + 1))
    (R ^ k) (t k) (alphaMixingCoef P Y (k + 1)) hTpos hX2 hZ2 rfl htZ hZ0 hcov
  simpa only [Real.norm_eq_abs] using this


end Main

end ExpAlphaLogMomentAux

open ExpAlphaLogMomentAux

/-- The covariance-control component of the Doukhan–Massart–Rio CLT. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) :=
  summable_covariance_of_exp_alpha_of_log_moment_aux P Y hY hstat hcent c a ha0 ha1 hα hmom
    (fun n k U V hU hV M hM hUb hVb => alpha_cov_bounded P Y hY n k U V hU hV M hM hUb hVb)
