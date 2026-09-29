-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_le_quarter_mul_rhoMixingCoef
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T07:27:41.168975+00:00
-- url     : https://prove2.me/submissions/fb346b3b-218b-4bfe-862c-09052c00b806

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-!
# The comparison `α(n) ≤ ρ(n) / 4`

For a probability measure the strong mixing coefficient is dominated by a quarter of the
maximal-correlation coefficient (R. C. Bradley, *Basic Properties of Strong Mixing
Conditions*, Probability Surveys 2 (2005), eq. (1.11)).

The proof tests the supremum defining `ρ` against the pair of indicator variables
`1_A, 1_B`: their covariance is exactly `P(A ∩ B) - P(A)P(B)`, and each of their standard
deviations is at most `1/2`, because `Var[1_A] = P(A)(1 - P(A)) ≤ 1/4`.  The degenerate case
`Var[1_A] = 0` is handled separately: it means `P(A) ∈ {0, 1}`, and then the covariance
vanishes outright.
-/

namespace AlphaRhoAux

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz: the covariance of two square-integrable functions is bounded by the
product of the standard deviations. -/
theorem abs_covariance_le_sqrt_variance_mul (P : Measure Ω) (U V : Ω → ℝ)
    (hUm : AEMeasurable U P) (hVm : AEMeasurable V P)
    (hU : MemLp (fun ω => U ω - ∫ x, U x ∂P) 2 P)
    (hV : MemLp (fun ω => V ω - ∫ x, V x ∂P) 2 P) :
    |cov[U, V; P]| ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by
  have hcs : |∫ ω, (U ω - ∫ x, U x ∂P) * (V ω - ∫ x, V x ∂P) ∂P| ≤
      Real.sqrt (∫ ω, (U ω - ∫ x, U x ∂P) ^ 2 ∂P) *
        Real.sqrt (∫ ω, (V ω - ∫ x, V x ∂P) ^ 2 ∂P) := by
    have h1 : |∫ ω, (U ω - ∫ x, U x ∂P) * (V ω - ∫ x, V x ∂P) ∂P| ≤
        ∫ ω, |U ω - ∫ x, U x ∂P| * |V ω - ∫ x, V x ∂P| ∂P := by
      calc |∫ ω, (U ω - ∫ x, U x ∂P) * (V ω - ∫ x, V x ∂P) ∂P|
          ≤ ∫ ω, |(U ω - ∫ x, U x ∂P) * (V ω - ∫ x, V x ∂P)| ∂P :=
            abs_integral_le_integral_abs
        _ = ∫ ω, |U ω - ∫ x, U x ∂P| * |V ω - ∫ x, V x ∂P| ∂P := by simp [abs_mul]
    have hU2 : MemLp (fun ω => |U ω - ∫ x, U x ∂P|) (ENNReal.ofReal 2) P := by
      simpa [ENNReal.ofReal_ofNat] using hU.abs
    have hV2 : MemLp (fun ω => |V ω - ∫ x, V x ∂P|) (ENNReal.ofReal 2) P := by
      simpa [ENNReal.ofReal_ofNat] using hV.abs
    have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
      (f := fun ω => |U ω - ∫ x, U x ∂P|) (g := fun ω => |V ω - ∫ x, V x ∂P|)
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) hU2 hV2
    refine h1.trans (h2.trans_eq ?_)
    have e : ∀ h : Ω → ℝ, (∫ ω, |h ω| ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
        = Real.sqrt (∫ ω, (h ω) ^ 2 ∂P) := by
      intro h
      rw [Real.sqrt_eq_rpow]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      show |h ω| ^ (2 : ℝ) = h ω ^ 2
      rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [e (fun ω => U ω - ∫ x, U x ∂P), e (fun ω => V ω - ∫ x, V x ∂P)]
  rwa [← covariance, ← variance_eq_integral hUm, ← variance_eq_integral hVm] at hcs

/-- Every element of the set defining `rhoMixingCoef` is at most `1`; no finiteness
assumption on the measure is needed. -/
theorem rho_set_le_one {E : Type*} [MeasurableSpace E] (P : Measure Ω) (Y : ℕ → Ω → E) (n : ℕ)
    {r : ℝ} (hr : r ∈ {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma Y (Set.Iic k)] U ∧
      Measurable[processSigma Y (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))}) :
    r ≤ 1 := by
  obtain ⟨k, U, V, -, -, hU2, hV2, rfl⟩ := hr
  rcases eq_or_ne (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) 0 with hzero | hne
  · simp [hzero]
  · have hVU : Var[U; P] ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hVV : Var[V; P] ≠ 0 := by
      intro h
      apply hne
      simp [h]
    -- a nonzero variance forces the centered variable to be square-integrable
    have hcU : MemLp (fun ω => U ω - ∫ x, U x ∂P) 2 P := by
      have hmeas : AEStronglyMeasurable (fun ω => U ω - ∫ x, U x ∂P) P :=
        hU2.aestronglyMeasurable.sub aestronglyMeasurable_const
      refine (memLp_two_iff_integrable_sq hmeas).2 ?_
      by_contra hcon
      exact hVU (by
        rw [variance_eq_integral hU2.aestronglyMeasurable.aemeasurable, integral_undef hcon])
    have hcV : MemLp (fun ω => V ω - ∫ x, V x ∂P) 2 P := by
      have hmeas : AEStronglyMeasurable (fun ω => V ω - ∫ x, V x ∂P) P :=
        hV2.aestronglyMeasurable.sub aestronglyMeasurable_const
      refine (memLp_two_iff_integrable_sq hmeas).2 ?_
      by_contra hcon
      exact hVV (by
        rw [variance_eq_integral hV2.aestronglyMeasurable.aemeasurable, integral_undef hcon])
    exact div_le_one_of_le₀ (abs_covariance_le_sqrt_variance_mul P U V
      hU2.aestronglyMeasurable.aemeasurable hV2.aestronglyMeasurable.aemeasurable hcU hcV)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem bddAbove_rho_set' {E : Type*} [MeasurableSpace E] (P : Measure Ω) (Y : ℕ → Ω → E)
    (n : ℕ) :
    BddAbove {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma Y (Set.Iic k)] U ∧
      Measurable[processSigma Y (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} :=
  ⟨1, fun _ hr => rho_set_le_one P Y n hr⟩

theorem zero_mem_rho_set {E : Type*} [MeasurableSpace E] (P : Measure Ω) (Y : ℕ → Ω → E)
    (n : ℕ) :
    (0 : ℝ) ∈ {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma Y (Set.Iic k)] U ∧
      Measurable[processSigma Y (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} := by
  refine ⟨0, (fun _ => 0), (fun _ => 0), measurable_const, measurable_const,
    MemLp.zero', MemLp.zero', ?_⟩
  simp [covariance]


/-- The variance of an indicator: `Var[1_A] = P(A)(1 - P(A))`. -/
theorem variance_indicator (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) :
    Var[A.indicator (fun _ => (1 : ℝ)); P] = (P A).toReal * (1 - (P A).toReal) := by
  have hmem : MemLp (A.indicator fun _ => (1 : ℝ)) 2 P := (memLp_const (1 : ℝ)).indicator hA
  have hint : ∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂P = (P A).toReal := by
    simp [integral_indicator hA, measureReal_def]
  have hsq : ((A.indicator (fun _ => (1 : ℝ))) ^ 2) = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : ω ∈ A <;>
      simp [Pi.pow_apply, Set.indicator_of_mem, Set.indicator_of_notMem, h]
  rw [variance_eq_sub hmem, hsq, hint]
  ring

/-- `Var[1_A] ≤ 1/4`. -/
theorem variance_indicator_le (P : Measure Ω) [IsProbabilityMeasure P] {A : Set Ω}
    (hA : MeasurableSet A) :
    Var[A.indicator (fun _ => (1 : ℝ)); P] ≤ 1 / 4 := by
  rw [variance_indicator P hA]
  nlinarith [sq_nonneg ((P A).toReal - 1 / 2)]

/-- The covariance of two indicators. -/
theorem covariance_indicator (P : Measure Ω) [IsProbabilityMeasure P] {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[A.indicator (fun _ => (1 : ℝ)), B.indicator (fun _ => (1 : ℝ)); P]
      = (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal := by
  have hmemA : MemLp (A.indicator fun _ => (1 : ℝ)) 2 P := (memLp_const (1 : ℝ)).indicator hA
  have hmemB : MemLp (B.indicator fun _ => (1 : ℝ)) 2 P := (memLp_const (1 : ℝ)).indicator hB
  have hprod : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * B.indicator (fun _ => (1 : ℝ)) ω)
      = (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hx : ω ∈ A <;> by_cases hy : ω ∈ B <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
  rw [covariance_eq_sub hmemA hmemB]
  simp [hprod, integral_indicator, hA, hB, hA.inter hB, measureReal_def]

/-- If the variance of `1_A` vanishes then the covariance with any indicator vanishes. -/
theorem covariance_indicator_eq_zero_of_measure_eq_zero_or_one (P : Measure Ω)
    [IsProbabilityMeasure P] {A B : Set Ω} (hA : MeasurableSet A)
    (h : (P A).toReal * (1 - (P A).toReal) = 0) :
    (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal = 0 := by
  rcases mul_eq_zero.1 h with h0 | h1
  · -- `P A = 0`
    have hA0 : P A = 0 := by
      have hne := measure_ne_top P A
      rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hne] at h0
    have hAB : P (A ∩ B) = 0 := measure_mono_null Set.inter_subset_left hA0
    simp [hAB, hA0]
  · -- `P A = 1`
    have hA1 : (P A).toReal = 1 := by linarith
    have hAtop : P A = 1 := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top P A), hA1, ENNReal.ofReal_one]
    have hcompl : P Aᶜ = 0 := by
      have hsum : P A + P Aᶜ = 1 := by
        rw [← measure_univ (μ := P), ← Set.union_compl_self A]
        exact (measure_union (Disjoint.symm disjoint_compl_left) hA.compl).symm
      rw [hAtop] at hsum
      simpa using hsum
    have hBsub : P B = P (A ∩ B) := by
      refine le_antisymm ?_ (measure_mono Set.inter_subset_right)
      have hsub : B ⊆ (A ∩ B) ∪ Aᶜ := by
        intro x hx
        by_cases hxa : x ∈ A
        · exact Or.inl ⟨hxa, hx⟩
        · exact Or.inr hxa
      calc P B ≤ P ((A ∩ B) ∪ Aᶜ) := measure_mono hsub
        _ ≤ P (A ∩ B) + P Aᶜ := measure_union_le _ _
        _ = P (A ∩ B) := by simp [hcompl]
    rw [← hBsub, hA1]
    ring


end AlphaRhoAux

/-- **`α(n) ≤ ρ(n) / 4`.** For a probability measure and a measurable process, the strong
mixing coefficient is at most a quarter of the maximal-correlation coefficient. -/
theorem solution {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → E) (hY : ∀ i, Measurable (Y i)) (n : ℕ) :
    alphaMixingCoef P Y n ≤ rhoMixingCoef P Y n / 4 := by
  have hrho0 : 0 ≤ rhoMixingCoef P Y n :=
    le_csSup (AlphaRhoAux.bddAbove_rho_set' P Y n) (AlphaRhoAux.zero_mem_rho_set P Y n)
  refine csSup_le ⟨0, ⟨0, ∅, ∅, @MeasurableSet.empty Ω (processSigma Y (Set.Iic 0)),
    @MeasurableSet.empty Ω (processSigma Y (Set.Ici (0 + n))), by simp⟩⟩ ?_
  rintro r ⟨k, A, B, hA, hB, rfl⟩
  -- the two indicator test functions
  have hle : ∀ s : Set ℕ, processSigma Y s ≤ (inferInstance : MeasurableSpace Ω) := by
    intro s
    refine iSup₂_le fun i _ => ?_
    exact (hY i).comap_le
  have hAamb : MeasurableSet A := hle (Set.Iic k) A hA
  have hBamb : MeasurableSet B := hle (Set.Ici (k + n)) B hB
  set U : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hU
  set V : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hV
  have hUmeas : Measurable[processSigma Y (Set.Iic k)] U := measurable_const.indicator hA
  have hVmeas : Measurable[processSigma Y (Set.Ici (k + n))] V := measurable_const.indicator hB
  have hUmem : MemLp U 2 P := (memLp_const (1 : ℝ)).indicator hAamb
  have hVmem : MemLp V 2 P := (memLp_const (1 : ℝ)).indicator hBamb
  have hcov : cov[U, V; P] = (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal :=
    AlphaRhoAux.covariance_indicator P hAamb hBamb
  have hVarU : Var[U; P] = (P A).toReal * (1 - (P A).toReal) := AlphaRhoAux.variance_indicator P hAamb
  have hVarV : Var[V; P] = (P B).toReal * (1 - (P B).toReal) := AlphaRhoAux.variance_indicator P hBamb
  rcases eq_or_ne (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) 0 with hzero | hnz
  · -- degenerate case: one of the two events has probability `0` or `1`
    have hcase : Var[U; P] = 0 ∨ Var[V; P] = 0 := by
      rcases mul_eq_zero.1 hzero with h | h
      · exact Or.inl (by
          have := Real.sqrt_eq_zero (variance_nonneg U P) |>.1 h
          exact this)
      · exact Or.inr (by
          have := Real.sqrt_eq_zero (variance_nonneg V P) |>.1 h
          exact this)
    have hzeroCov : (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal = 0 := by
      rcases hcase with h | h
      · exact AlphaRhoAux.covariance_indicator_eq_zero_of_measure_eq_zero_or_one P hAamb
          (by rwa [hVarU] at h)
      · have := AlphaRhoAux.covariance_indicator_eq_zero_of_measure_eq_zero_or_one (B := A) P hBamb
          (by rwa [hVarV] at h)
        rw [Set.inter_comm] at this
        linarith [this]
    rw [hzeroCov]
    simpa using div_nonneg hrho0 (by norm_num : (0:ℝ) ≤ 4)
  · -- generic case: the correlation quotient is an element of the `ρ` supremum
    have hmem : |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))
        ∈ {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
          Measurable[processSigma Y (Set.Iic k)] U ∧
          Measurable[processSigma Y (Set.Ici (k + n))] V ∧
          MemLp U 2 P ∧ MemLp V 2 P ∧
          r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} :=
      ⟨k, U, V, hUmeas, hVmeas, hUmem, hVmem, rfl⟩
    have hquot : |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))
        ≤ rhoMixingCoef P Y n := le_csSup (AlphaRhoAux.bddAbove_rho_set' P Y n) hmem
    have hpos : 0 < Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) :=
      lt_of_le_of_ne (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Ne.symm hnz)
    have habs : |cov[U, V; P]|
        ≤ rhoMixingCoef P Y n * (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) :=
      (div_le_iff₀ hpos).1 hquot
    have hsU : Real.sqrt (Var[U; P]) ≤ 1 / 2 := by
      have h4 : Var[U; P] ≤ (1 / 2 : ℝ) ^ 2 := by
        have := AlphaRhoAux.variance_indicator_le P hAamb; nlinarith
      have hs := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)] at hs
    have hsV : Real.sqrt (Var[V; P]) ≤ 1 / 2 := by
      have h4 : Var[V; P] ≤ (1 / 2 : ℝ) ^ 2 := by
        have := AlphaRhoAux.variance_indicator_le P hBamb; nlinarith
      have hs := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)] at hs
    have hprod : Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) ≤ 1 / 4 := by
      nlinarith [Real.sqrt_nonneg (Var[U; P]), Real.sqrt_nonneg (Var[V; P])]
    calc |(P (A ∩ B)).toReal - (P A).toReal * (P B).toReal| = |cov[U, V; P]| := by rw [hcov]
      _ ≤ rhoMixingCoef P Y n * (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := habs
      _ ≤ rhoMixingCoef P Y n * (1 / 4) := by
          exact mul_le_mul_of_nonneg_left hprod hrho0
      _ = rhoMixingCoef P Y n / 4 := by ring

