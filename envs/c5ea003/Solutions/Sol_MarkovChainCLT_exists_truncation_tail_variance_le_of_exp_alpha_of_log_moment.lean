-- Prove2me | solution 1 for MarkovChainCLT.exists_truncation_tail_variance_le_of_exp_alpha_of_log_moment
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-05T11:41:56.75292+00:00
-- url     : https://prove2.me/submissions/19d9b406-91de-437d-9688-441bca923e2b

/-
Tail-variance estimate for the MC CLT mission.
The truncation helpers through `alphaMixingCoef_nonneg` are reused from
Gabewhigham's accepted covariance proof, submission
b4ddeb01-53ae-430c-a166-0197d09d3998. The uniform-in-cutoff argument below is new.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_memLp_two_and_logMoment_sub_const
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ProbabilityTheory ENNReal Topology

namespace TailVariance

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



/-- Variance expansion adapted from WillR's accepted submission
22190ef3-0b53-4770-9441-4c54c00d05a1. Absolute covariance summability
bounds every partial sum, rather than only its asymptotic variance. -/
theorem partialSum_sq_le
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P) ≤
      ((∫ ω, Y 0 ω ^ 2 ∂P) + 2 * ∑' k, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|) * n := by
  have hmap : ∀ k, P.map (Y k) = P.map (Y 0) := by
    intro k
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have hmemLp : ∀ k, MemLp (Y k) 2 P := by
    intro k
    have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
      (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) (hY 0).aemeasurable).2 hL2
    have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by rw [hmap k]; exact h0
    exact (memLp_map_measure_iff (measurable_id.aestronglyMeasurable) (hY k).aemeasurable).1 hk
  have hmean : ∀ k, ∫ ω, Y k ω ∂P = 0 := by
    intro k
    have h1 : ∫ x, x ∂(P.map (Y k)) = ∫ ω, Y k ω ∂P :=
      integral_map (hY k).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    have h2 : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
      integral_map (hY 0).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
    rw [← h1, hmap k, h2, hcent]
  set c : ℕ → ℝ := fun k => ∫ ω, Y 0 ω * Y k ω ∂P with hc
  have hc_def : ∀ k, c k = ∫ ω, Y 0 ω * Y k ω ∂P := fun k => rfl
  have hpair : ∀ i d : ℕ, ∫ ω, Y i ω * Y (i + d) ω ∂P = c d := by
    intro i d
    have hgm : Measurable (fun f : ℕ → ℝ => f 0 * f d) :=
      (measurable_pi_apply 0).mul (measurable_pi_apply d)
    have hmeasi : Measurable (fun ω n => Y (n + i) ω) :=
      measurable_pi_lambda _ fun n => hY (n + i)
    have hmeas0 : Measurable (fun ω n => Y n ω) :=
      measurable_pi_lambda _ fun n => hY n
    have e1 : ∫ f, f 0 * f d ∂(Measure.map (fun ω n => Y (n + i) ω) P)
        = ∫ ω, Y i ω * Y (i + d) ω ∂P := by
      rw [integral_map hmeasi.aemeasurable hgm.aestronglyMeasurable]
      apply integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show Y (0 + i) ω * Y (d + i) ω = Y i ω * Y (i + d) ω
      rw [Nat.zero_add, Nat.add_comm d i]
    have e2 : ∫ f, f 0 * f d ∂(Measure.map (fun ω n => Y n ω) P)
        = ∫ ω, Y 0 ω * Y d ω ∂P := by
      rw [integral_map hmeas0.aemeasurable hgm.aestronglyMeasurable]
    rw [hc_def d]
    rw [hstat i] at e1
    rw [e2] at e1
    exact e1.symm
  have hcov : ∀ i j : ℕ, i ≤ j → cov[Y i, Y j; P] = c (j - i) := by
    intro i j hij
    have hji : j = i + (j - i) := (Nat.add_sub_cancel' hij).symm
    rw [covariance]
    simp only [hmean i, hmean j, sub_zero]
    conv_lhs => rw [hji]
    exact hpair i (j - i)
  have hF : ∀ n : ℕ, (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cov[Y i, Y j; P])
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hcol : ∑ i ∈ Finset.range n, cov[Y i, Y n; P]
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e1 : ∀ i ∈ Finset.range n, cov[Y i, Y n; P] = c ((n - 1 - i) + 1) := by
          intro i hi
          rw [Finset.mem_range] at hi
          have hiN : i ≤ n := Nat.le_of_lt hi
          have h := hcov i n hiN
          have hni : n - i = (n - 1 - i) + 1 := by omega
          rw [hni] at h
          exact h
        rw [Finset.sum_congr rfl e1]
        exact Finset.sum_range_reflect (fun j => c (j + 1)) n
      have hrow : ∑ j ∈ Finset.range n, cov[Y n, Y j; P]
          = ∑ k ∈ Finset.range n, c (k + 1) := by
        have e : ∀ j ∈ Finset.range n, cov[Y n, Y j; P] = cov[Y j, Y n; P] :=
          fun j _ => covariance_comm (Y n) (Y j)
        rw [Finset.sum_congr rfl e]
        exact hcol
      have hdiag : cov[Y n, Y n; P] = c 0 := by
        have h := hcov n n le_rfl
        simpa using h
      rw [Finset.sum_range_succ]
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib, ih, hcol, hrow, hdiag]
      push_cast
      ring
  have hV : ∀ n : ℕ, Var[∑ i ∈ Finset.range n, Y i; P]
      = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, cov[Y i, Y j; P] :=
    fun n => variance_sum' (fun i _ => hmemLp i)
  have hVD : ∀ n : ℕ, Var[∑ i ∈ Finset.range n, Y i; P]
      = (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1) :=
    fun n => (hV n).trans (hF n)

  have hsm : ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ∂P = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmemLp i).integrable (by norm_num))]
    simp [hmean]
  have hvm : Var[∑ i ∈ Finset.range n, Y i; P] =
      ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P := by
    rw [variance_eq_integral (memLp_finsetSum' _ (fun i _ => hmemLp i)).aemeasurable]
    simp only [Finset.sum_apply, hsm, sub_zero]
  have hc0 : c 0 = ∫ ω, Y 0 ω ^ 2 ∂P := by simp only [hc, pow_two]
  have hbound : ∀ m : ℕ, ∑ k ∈ Finset.range m, c (k + 1) ≤ ∑' k, |c (k + 1)| := by
    intro m
    exact (Finset.sum_le_sum (fun k _ => le_abs_self _)).trans
      (hsum.sum_le_tsum (Finset.range m) (fun k _ => abs_nonneg _))
  rw [← hvm, hVD n]
  calc (n : ℝ) * c 0 + 2 * ∑ m ∈ Finset.range n, ∑ k ∈ Finset.range m, c (k + 1)
      ≤ (n : ℝ) * c 0 + 2 * ∑ _m ∈ Finset.range n, ∑' k, |c (k + 1)| := by
        gcongr with m hm
        exact hbound m
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc, pow_two]; ring

/-- A product's first absolute moment is bounded by the common second moment. -/
theorem abs_integral_mul_le_second
    (P : Measure Ω) [IsProbabilityMeasure P] (X Z : Ω → ℝ)
    (hX : MemLp X 2 P) (hZ : MemLp Z 2 P)
    (heq : ∫ ω, Z ω ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P) :
    |∫ ω, X ω * Z ω ∂P| ≤ ∫ ω, X ω ^ 2 ∂P := by
  calc |∫ ω, X ω * Z ω ∂P| ≤ ∫ ω, |X ω * Z ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (X ω ^ 2 + Z ω ^ 2) / 2 ∂P := by
      apply integral_mono (hX.integrable_mul hZ).abs
        ((hX.integrable_sq.add hZ.integrable_sq).div_const 2)
      intro ω
      change |X ω * Z ω| ≤ (X ω ^ 2 + Z ω ^ 2) / 2
      rw [abs_mul]
      nlinarith [sq_nonneg (|X ω| - |Z ω|), sq_abs (X ω), sq_abs (Z ω)]
    _ = ∫ ω, X ω ^ 2 ∂P := by
      rw [integral_div, integral_add hX.integrable_sq hZ.integrable_sq, heq]
      ring

noncomputable def high (T x : ℝ) : ℝ := if T < |x| then x else 0

lemma measurable_high (T : ℝ) : Measurable (high T) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_abs) measurable_id measurable_const

lemma high_abs_le (T x : ℝ) : |high T x| ≤ |x| := by
  unfold high
  split_ifs <;> simp [abs_nonneg]

lemma high_sq (T x : ℝ) : high T x ^ 2 = tailSq T x := by
  by_cases h : T < |x|
  · simp [high, tailSq, h, not_le.mpr h]
  · simp [high, tailSq, h, le_of_not_gt h]

lemma tailSq_mono_abs {S x w : ℝ} (h : |x| ≤ |w|) : tailSq S x ≤ tailSq S w := by
  by_cases hx : |x| ≤ S
  · simpa [tailSq, hx] using tailSq_nonneg S w
  · have hw : ¬ |w| ≤ S := fun hw => hx (h.trans hw)
    simp only [tailSq, hx, hw, if_false]
    nlinarith [sq_abs x, sq_abs w, abs_nonneg x, abs_nonneg w]

lemma memLp_high (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hX2 : MemLp X 2 P) (T : ℝ) : MemLp (fun ω => high T (X ω)) 2 P := by
  exact hX2.mono ((measurable_high T).comp hX).aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using high_abs_le T (X ω))

lemma tendsto_integral_high_sq (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (hX2 : MemLp X 2 P) :
    Tendsto (fun N : ℕ => ∫ ω, high (N : ℝ) (X ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => high (N : ℝ) (X ω) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    apply ae_of_all
    intro ω
    obtain ⟨K, hK⟩ := exists_nat_gt |X ω|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with N hN
    have hx : ¬ (N : ℝ) < |X ω| := by
      have hcast : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    simp [high, hx]
  have hh := tendsto_integral_of_dominated_convergence (fun ω => X ω ^ 2)
    (fun N => (((measurable_high (N : ℝ)).comp hX).pow_const 2).aestronglyMeasurable)
    hX2.integrable_sq (fun N => ae_of_all _ fun ω => ?_) hlim
  · simpa using hh
  change ‖high (N : ℝ) (X ω) ^ 2‖ ≤ X ω ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), high_sq]
  exact tailSq_le_sq _ _

/-- A common log-moment envelope gives one summable covariance bound for
an entire family of centered exponentially mixing processes. -/
theorem exists_uniform_covariance_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → ℕ → Ω → ℝ)
    (hZ : ∀ N i, Measurable (Z N i))
    (hstat : ∀ N, IsStrictlyStationary P (Z N))
    (hcent : ∀ N, ∫ ω, Z N 0 ω ∂P = 0)
    (hL2 : ∀ N, MemLp (Z N 0) 2 P)
    (W : Ω → ℝ) (hW : Measurable W)
    (hmom : Integrable (fun ω => W ω ^ 2 * Real.posLog |W ω|) P)
    (henv : ∀ N ω, |Z N 0 ω| ≤ |W ω|)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hal : ∀ N n, alphaMixingCoef P (Z N) n ≤ c * a ^ n) :
    ∃ B : ℕ → ℝ, Summable B ∧ (∀ k, 0 ≤ B k) ∧
      ∀ N k, |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P| ≤ B k := by
  have hc0 : 0 ≤ c := by
    have hh := (alphaMixingCoef_nonneg P (Z 0) 0).trans (hal 0 0)
    simpa using hh
  have h1a : (0 : ℝ) < 1 + a := by linarith
  let R : ℝ := Real.sqrt (2 / (1 + a))
  have hR2 : R ^ 2 = 2 / (1 + a) := Real.sq_sqrt (by positivity)
  have hR1 : 1 < R := by
    have hh : (1 : ℝ) < 2 / (1 + a) := by rw [lt_div_iff₀ h1a]; linarith
    nlinarith [Real.sqrt_nonneg (2 / (1 + a)), hR2]
  have hR0 : 0 < R := lt_trans zero_lt_one hR1
  let q : ℝ := a * R ^ 2
  have hq0 : 0 ≤ q := mul_nonneg ha0 (sq_nonneg R)
  have hq1 : q < 1 := by
    dsimp [q]
    rw [hR2, mul_div_assoc', div_lt_one h1a]
    linarith
  let t : ℕ → ℝ := fun k => ∫ ω, tailSq (R ^ k) (W ω) ∂P
  have htail : Summable t := summable_integral_tailSq P W hW hmom hR1
  let B : ℕ → ℝ := fun k => 4 * c * a * q ^ k + 3 * t k
  have hB : Summable B :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (4 * c * a)).add (htail.mul_left 3)
  have ht0 : ∀ k, 0 ≤ t k := fun k => integral_nonneg fun ω => tailSq_nonneg _ _
  have hB0 : ∀ k, 0 ≤ B k := by
    intro k
    have ht := ht0 k
    dsimp [B]
    positivity
  refine ⟨B, hB, hB0, ?_⟩
  intro N k
  have hid := identDistrib_coord P (Z N) (hZ N) (hstat N) (k + 1)
  have hZ2 : MemLp (Z N (k + 1)) 2 P := hid.memLp_iff.mpr (hL2 N)
  have hZ0 : ∫ ω, Z N (k + 1) ω ∂P = 0 := hid.integral_eq.trans (hcent N)
  let tN : ℝ := ∫ ω, tailSq (R ^ k) (Z N 0 ω) ∂P
  have htZ : ∫ ω, tailSq (R ^ k) (Z N (k + 1) ω) ∂P = tN :=
    (hid.comp (measurable_tailSq (R ^ k))).integral_eq
  have hTpos : (0 : ℝ) < R ^ k := by positivity
  have hcov : |cov[fun ω => truncAt (R ^ k) (Z N 0 ω),
      fun ω => truncAt (R ^ k) (Z N (k + 1) ω); P]|
      ≤ 4 * (R ^ k) ^ 2 * alphaMixingCoef P (Z N) (k + 1) := by
    exact alpha_cov_bounded P (Z N) (hZ N) (k + 1) 0 _ _
      ((measurable_truncAt _).comp (measurable_coord (Z N) (Set.Iic 0) 0 (by simp)))
      ((measurable_truncAt _).comp
        (measurable_coord (Z N) (Set.Ici (0 + (k + 1))) (k + 1) (by simp)))
      (R ^ k) hTpos.le (fun ω => truncAt_bound hTpos.le _)
      (fun ω => truncAt_bound hTpos.le _)
  have hfirst := abs_integral_mul_le_of_cov_bound P (Z N 0) (Z N (k + 1))
    (hZ N 0) (hZ N (k + 1)) (R ^ k) tN (alphaMixingCoef P (Z N) (k + 1))
    hTpos (hL2 N) hZ2 rfl htZ hZ0 hcov
  have hW2 := memLp_two_of_logMoment P W hW hmom
  have htailInt : ∀ (X : Ω → ℝ), Measurable X → MemLp X 2 P →
      Integrable (fun ω => tailSq (R ^ k) (X ω)) P := by
    intro X hX hX2
    exact hX2.integrable_sq.mono' ((measurable_tailSq _).comp hX).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (tailSq_nonneg _ _)]
        exact tailSq_le_sq _ _)
  have htN : tN ≤ t k :=
    integral_mono (htailInt _ (hZ N 0) (hL2 N)) (htailInt W hW hW2)
      (fun ω => tailSq_mono_abs (henv N ω))
  calc |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|
      ≤ 4 * (R ^ k) ^ 2 * alphaMixingCoef P (Z N) (k + 1) + 3 * tN := hfirst
    _ ≤ 4 * (R ^ k) ^ 2 * (c * a ^ (k + 1)) + 3 * t k := by
      gcongr
      exact hal N (k + 1)
    _ = B k := by
      dsimp [B, q]
      rw [mul_pow, ← pow_mul, ← pow_mul]
      ring_nf

end Main
end TailVariance

open TailVariance

/-- The centered high part contributes arbitrarily little variance per sample. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (c a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hα : ∀ n, alphaMixingCoef P Y n ≤ c * a ^ n)
    (hmom : Integrable (fun ω => (Y 0 ω) ^ 2 * Real.posLog |Y 0 ω|) P)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ,
      ∫ ω, (∑ i ∈ Finset.range n,
        ((if T < |Y i ω| then Y i ω else 0)
          - ∫ ω', (if T < |Y 0 ω'| then Y 0 ω' else 0) ∂P)) ^ 2 ∂P ≤ ε * n := by
  have hY02 : MemLp (Y 0) 2 P := memLp_two_of_logMoment P (Y 0) (hY 0) hmom
  have hYi2 : ∀ i, MemLp (Y i) 2 P := fun i =>
    (identDistrib_coord P Y hY hstat i).memLp_iff.mpr hY02
  let m : ℕ → ℝ := fun N => ∫ ω, high (N : ℝ) (Y 0 ω) ∂P
  let g : ℕ → ℝ → ℝ := fun N x => high (N : ℝ) x - m N
  let Z : ℕ → ℕ → Ω → ℝ := fun N i ω => g N (Y i ω)
  have hg : ∀ N, Measurable (g N) := fun N => (measurable_high (N : ℝ)).sub_const (m N)
  have hZ : ∀ N i, Measurable (Z N i) := fun N i => (hg N).comp (hY i)
  have hHs : ∀ (N i : ℕ), MemLp (fun ω => high (N : ℝ) (Y i ω)) 2 P :=
    fun N i => memLp_high P (Y i) (hY i) (hYi2 i) (N : ℝ)
  have hZ2 : ∀ N i, MemLp (Z N i) 2 P := fun N i => (hHs N i).sub (memLp_const (m N))
  have hZstat : ∀ N, IsStrictlyStationary P (Z N) := fun N =>
    isStrictlyStationary_comp_of_measurable P Y hY hstat (g N) (hg N)
  have hZcent : ∀ N, ∫ ω, Z N 0 ω ∂P = 0 := by
    intro N
    dsimp [Z, g]
    rw [integral_sub ((hHs N 0).integrable (by norm_num)) (integrable_const (m N))]
    simp [m]
  have hZα : ∀ N k, alphaMixingCoef P (Z N) k ≤ c * a ^ k := by
    intro N k
    exact (alphaMixingCoef_comp_nonneg_le_of_finite P Y (g N) (hg N) k).2.trans (hα k)
  let C : ℝ := ∫ ω, |Y 0 ω| ∂P
  have hC0 : 0 ≤ C := integral_nonneg fun ω => abs_nonneg _
  have hm : ∀ N, |m N| ≤ C := by
    intro N
    exact abs_integral_le_integral_abs.trans
      (integral_mono ((hHs N 0).integrable (by norm_num)).abs
        (hY02.integrable (by norm_num)).abs (fun ω => high_abs_le (N : ℝ) (Y 0 ω)))
  let W : Ω → ℝ := fun ω => |Y 0 ω| + C
  have hW : Measurable W := (hY 0).abs.add_const C
  have hWmom : Integrable (fun ω => W ω ^ 2 * Real.posLog |W ω|) P := by
    have habsmom : Integrable (fun ω => |Y 0 ω| ^ 2 * Real.posLog |(|Y 0 ω|)|) P := by
      simpa only [sq_abs, abs_abs] using hmom
    have hh := (memLp_two_and_logMoment_sub_const P (fun ω => |Y 0 ω|)
      (hY 0).abs habsmom (-C)).2
    simpa only [sub_neg_eq_add] using hh
  have henv : ∀ N ω, |Z N 0 ω| ≤ |W ω| := by
    intro N ω
    have hw : 0 ≤ W ω := add_nonneg (abs_nonneg _) hC0
    rw [abs_of_nonneg hw]
    calc |Z N 0 ω| ≤ |high (N : ℝ) (Y 0 ω)| + |m N| := by
          simpa only [Z, g, sub_zero, zero_sub, abs_neg] using
            (abs_sub_le (high (N : ℝ) (Y 0 ω)) 0 (m N))
      _ ≤ W ω := add_le_add (high_abs_le (N : ℝ) (Y 0 ω)) (hm N)
  obtain ⟨B, hB, hB0, hbound⟩ := exists_uniform_covariance_bound P Z hZ hZstat hZcent
    (fun N => hZ2 N 0) W hW hWmom henv c a ha0 ha1 hZα
  let v : ℕ → ℝ := fun N => ∫ ω, Z N 0 ω ^ 2 ∂P
  have hv0 : ∀ N, 0 ≤ v N := fun N => integral_nonneg fun ω => sq_nonneg _
  have hvle : ∀ N, v N ≤ ∫ ω, high (N : ℝ) (Y 0 ω) ^ 2 ∂P := by
    intro N
    change (∫ ω, (high (N : ℝ) (Y 0 ω) - m N) ^ 2 ∂P) ≤ _
    rw [show (∫ ω, (high (N : ℝ) (Y 0 ω) - m N) ^ 2 ∂P) =
      Var[fun ω => high (N : ℝ) (Y 0 ω); P] from
        (variance_eq_integral ((measurable_high (N : ℝ)).comp (hY 0)).aemeasurable).symm]
    exact variance_le_expectation_sq ((measurable_high (N : ℝ)).comp (hY 0)).aestronglyMeasurable
  have hvlim : Tendsto v atTop (𝓝 0) :=
    squeeze_zero hv0 hvle (tendsto_integral_high_sq P (Y 0) (hY 0) hY02)
  let r : ℕ → ℕ → ℝ := fun N k => |∫ ω, Z N 0 ω * Z N (k + 1) ω ∂P|
  have hrle : ∀ N k, r N k ≤ v N := by
    intro N k
    apply abs_integral_mul_le_second P _ _ (hZ2 N 0) (hZ2 N (k + 1))
    exact ((identDistrib_coord P (Z N) (hZ N) (hZstat N) (k + 1)).comp
      (measurable_id.pow_const 2)).integral_eq
  have hrlim : ∀ k, Tendsto (fun N => r N k) atTop (𝓝 0) := fun k =>
    squeeze_zero (fun N => abs_nonneg _) (fun N => hrle N k) hvlim
  have hrlim_sum : Tendsto (fun N => ∑' k, r N k) atTop (𝓝 0) := by
    have hh := tendsto_tsum_of_dominated_convergence hB hrlim
      (Filter.Eventually.of_forall (fun N k => ?_))
    · simpa using hh
    simpa only [Real.norm_eq_abs, r, abs_abs] using hbound N k
  have hrsum : ∀ N, Summable (r N) := fun N =>
    hB.of_norm_bounded (fun k => by simpa only [Real.norm_eq_abs, r, abs_abs] using hbound N k)
  have htot : Tendsto (fun N => v N + 2 * ∑' k, r N k) atTop (𝓝 0) := by
    simpa using hvlim.add (hrlim_sum.const_mul 2)
  have hevent : ∀ᶠ N in atTop, v N + 2 * ∑' k, r N k < ε :=
    htot.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN, hsmall⟩ := (eventually_ge_atTop 1 |>.and hevent).exists
  refine ⟨(N : ℝ), by exact_mod_cast (show 0 < N by omega), ?_⟩
  intro n
  have hh := partialSum_sq_le P (Z N) (hZ N) (hZstat N) (hZcent N) (hZ2 N 0) (hrsum N) n
  have hlast : (v N + 2 * ∑' k, r N k) * (n : ℝ) ≤ ε * n :=
    mul_le_mul_of_nonneg_right hsmall.le (Nat.cast_nonneg n)
  exact hh.trans hlast
