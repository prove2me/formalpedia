-- Prove2me | solution 1 for MarkovChainCLT.uniformIntegrable_sq_partialSum_of_summable_rho
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:04:55.060661+00:00
-- url     : https://prove2.me/submissions/5b366a5e-0a3b-46f3-ae2f-3689f4448c20

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Theorems.Thm_MeasureTheory_tendsto_integral_sq_sub_truncation
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Theorems.Thm_MarkovChainCLT_var_partialSum_div_tendsto_of_summable_cov
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum.RealSqrt
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith.NNRealPreprocessor

section UIComponent1

/- Full generic Cauchy-Schwarz/rho-supremum helpers from Gabewhigham's accepted
submission a1cb1e12-f123-4e20-92be-d71f233bbe7b, theorem
6d2e5fd1-844b-4232-8b61-9e52f5311b5d. Only the enclosing namespace is renamed.
Original source and exact range mapping: rho-helper-provenance.json. -/

open MeasureTheory ProbabilityTheory MarkovChainCLT

namespace SummableRhoUI

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Cauchy–Schwarz for the integral of a product of two square-integrable functions. -/
lemma abs_integral_mul_le (P : Measure Ω) (f g : Ω → ℝ)
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |∫ ω, f ω * g ω ∂P| ≤ Real.sqrt (∫ ω, (f ω) ^ 2 ∂P) * Real.sqrt (∫ ω, (g ω) ^ 2 ∂P) := by
  have h1 : |∫ ω, f ω * g ω ∂P| ≤ ∫ ω, |f ω| * |g ω| ∂P := by
    calc |∫ ω, f ω * g ω ∂P| ≤ ∫ ω, |f ω * g ω| ∂P := abs_integral_le_integral_abs
    _ = ∫ ω, |f ω| * |g ω| ∂P := by simp [abs_mul]
  have hf2 : MemLp (fun ω => |f ω|) (ENNReal.ofReal 2) P := by
    simpa [ENNReal.ofReal_ofNat] using hf.abs
  have hg2 : MemLp (fun ω => |g ω|) (ENNReal.ofReal 2) P := by
    simpa [ENNReal.ofReal_ofNat] using hg.abs
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P) Real.HolderConjugate.two_two
    (f := fun ω => |f ω|) (g := fun ω => |g ω|)
    (Filter.Eventually.of_forall fun ω => abs_nonneg _)
    (Filter.Eventually.of_forall fun ω => abs_nonneg _) hf2 hg2
  refine h1.trans (h2.trans_eq ?_)
  have e : ∀ h : Ω → ℝ, (∫ ω, |h ω| ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ ω, (h ω) ^ 2 ∂P) := by
    intro h
    rw [Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show |h ω| ^ (2 : ℝ) = h ω ^ 2
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [e f, e g]

/-- Every element of the set defining `rhoMixingCoef` is at most `1`, so that set is bounded
above and the supremum can be bounded from below by any of its elements. -/
lemma bddAbove_rho_set (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (n : ℕ) :
    BddAbove {r | ∃ k : ℕ, ∃ U V : Ω → ℝ,
      Measurable[processSigma Y (Set.Iic k)] U ∧
      Measurable[processSigma Y (Set.Ici (k + n))] V ∧
      MemLp U 2 P ∧ MemLp V 2 P ∧
      r = |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]))} := by
  refine ⟨1, ?_⟩
  rintro r ⟨k, U, V, -, -, hU2, hV2, rfl⟩
  have hUi : Integrable U P := hU2.integrable (by norm_num)
  have hVi : Integrable V P := hV2.integrable (by norm_num)
  have hU' : MemLp (fun ω => U ω - ∫ x, U x ∂P) 2 P := hU2.sub (memLp_const _)
  have hV' : MemLp (fun ω => V ω - ∫ x, V x ∂P) 2 P := hV2.sub (memLp_const _)
  have hcov : |cov[U, V; P]| ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by
    have := abs_integral_mul_le P (fun ω => U ω - ∫ x, U x ∂P) (fun ω => V ω - ∫ x, V x ∂P)
      hU' hV'
    rwa [← covariance, ← variance_eq_integral hUi.aemeasurable,
      ← variance_eq_integral hVi.aemeasurable] at this
  have hnn : 0 ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact div_le_one_of_le₀ hcov hnn

end SummableRhoUI

end UIComponent1

section UIComponent2

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def naturalFiltration (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) :
    Filtration ℕ mΩ := Filtration.natural Y fun n => (hY n).stronglyMeasurable

theorem naturalFiltration_eq (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (n : ℕ) :
    naturalFiltration Y hY n = processSigma Y (Set.Iic n) := rfl

theorem rho_nonneg (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (k : ℕ) :
    0 ≤ rhoMixingCoef P Y k := by
  apply le_csSup (bddAbove_rho_set P Y k)
  refine ⟨0, fun _ => 0, fun _ => 0, measurable_const, measurable_const,
    memLp_const 0, memLp_const 0, ?_⟩
  simp [covariance]

theorem abs_covariance_le_rho (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (n k : ℕ) (U V : Ω → ℝ)
    (hUm : Measurable[processSigma Y (Set.Iic n)] U)
    (hVm : Measurable[processSigma Y (Set.Ici (n + k))] V)
    (hU : MemLp U 2 P) (hV : MemLp V 2 P) :
    |cov[U, V; P]| ≤ rhoMixingCoef P Y k *
      (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) := by
  have hden : 0 ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by positivity
  have hcs : |cov[U, V; P]| ≤ Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P]) := by
    have h := abs_integral_mul_le P (fun ω => U ω - ∫ x, U x ∂P)
      (fun ω => V ω - ∫ x, V x ∂P) (hU.sub (memLp_const _)) (hV.sub (memLp_const _))
    rwa [← covariance, ← variance_eq_integral hU.aestronglyMeasurable.aemeasurable,
      ← variance_eq_integral hV.aestronglyMeasurable.aemeasurable] at h
  rcases eq_or_lt_of_le hden with hz | hp
  · rw [← hz] at hcs ⊢
    simpa using hcs
  · have h := le_csSup (bddAbove_rho_set P Y k)
      (show |cov[U, V; P]| / (Real.sqrt (Var[U; P]) * Real.sqrt (Var[V; P])) ∈
        {r | ∃ j : ℕ, ∃ A B : Ω → ℝ,
          Measurable[processSigma Y (Set.Iic j)] A ∧
          Measurable[processSigma Y (Set.Ici (j + k))] B ∧
          MemLp A 2 P ∧ MemLp B 2 P ∧
          r = |cov[A, B; P]| / (Real.sqrt (Var[A; P]) * Real.sqrt (Var[B; P]))} from
        ⟨n, U, V, hUm, hVm, hU, hV, rfl⟩)
    exact (div_le_iff₀ hp).mp h

theorem norm_toLp_sq_integral (P : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with ω hω
  simp [hω, Real.norm_eq_abs, sq_abs]

theorem sqrt_integral_sq_eq_norm_toLp (P : Measure Ω) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂P) = ‖hf.toLp f‖ := by
  rw [← norm_toLp_sq_integral P f hf, Real.sqrt_sq (norm_nonneg _)]

theorem condExp_norm_le_rho (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (V : Ω → ℝ)
    (hVm : Measurable[processSigma Y (Set.Ici (n + k))] V)
    (hV : MemLp V 2 P) (hcent : ∫ ω, V ω ∂P = 0) :
    ‖(hV.condExp (m := naturalFiltration Y hY n)).toLp
        (P[V | naturalFiltration Y hY n])‖ ≤
      rhoMixingCoef P Y k * ‖hV.toLp V‖ := by
  let m := naturalFiltration Y hY n
  letI : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := (naturalFiltration Y hY).le n
  let U := P[V | m]
  have hU : MemLp U 2 P := hV.condExp
  have hUm : Measurable[m] U := stronglyMeasurable_condExp.measurable
  have hUi : Integrable U P := hU.integrable (by norm_num)
  have hVi : Integrable V P := hV.integrable (by norm_num)
  have hUcent : ∫ ω, U ω ∂P = 0 := (integral_condExp hm).trans hcent
  have hprod : ∫ ω, U ω * V ω ∂P = ∫ ω, U ω ^ 2 ∂P := by
    calc
      ∫ ω, U ω * V ω ∂P = ∫ ω, (P[U * V | m]) ω ∂P := (integral_condExp hm).symm
      _ = ∫ ω, U ω ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [condExp_mul_of_stronglyMeasurable_left
          (show StronglyMeasurable[m] U from stronglyMeasurable_condExp)
          (hU.integrable_mul hV) hVi] with ω hω
        simpa [U, pow_two] using hω
  have hvarU : Var[U; P] = ∫ ω, U ω ^ 2 ∂P := by
    rw [variance_eq_integral hUi.aemeasurable, hUcent]
    simp
  have hvarV : Var[V; P] = ∫ ω, V ω ^ 2 ∂P := by
    rw [variance_eq_integral hVi.aemeasurable, hcent]
    simp
  have hcov : cov[U, V; P] = ∫ ω, U ω ^ 2 ∂P := by
    rw [covariance, hUcent, hcent]
    simpa using hprod
  have h := abs_covariance_le_rho P Y n k U V hUm hVm hU hV
  rw [hcov, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _), hvarU, hvarV,
    sqrt_integral_sq_eq_norm_toLp P U hU, sqrt_integral_sq_eq_norm_toLp P V hV,
    ← norm_toLp_sq_integral P U hU] at h
  change ‖hU.toLp U‖ ≤ rhoMixingCoef P Y k * ‖hV.toLp V‖
  by_cases hz : ‖hU.toLp U‖ = 0
  · rw [hz]
    exact mul_nonneg (rho_nonneg P Y k) (norm_nonneg _)
  · have hp : 0 < ‖hU.toLp U‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith [h]

end SummableRhoUI

end UIComponent2

section UIComponent3

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} {m m₁ m₂ mΩ : MeasurableSpace Ω}

noncomputable def conditionalL2 (P : @Measure Ω mΩ) (hm : m ≤ mΩ) :
    Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
  (lpMeas ℝ ℝ m 2 P).subtypeL.comp (condExpL2 ℝ ℝ hm)

theorem conditionalL2_adapted (P : @Measure Ω mΩ) (hm : m ≤ mΩ) (f : Lp ℝ 2 P) :
    AEStronglyMeasurable[m] (conditionalL2 P hm f) P :=
  aestronglyMeasurable_condExpL2 hm f

theorem conditionalL2_norm_le (P : @Measure Ω mΩ) (hm : m ≤ mΩ) (f : Lp ℝ 2 P) :
    ‖conditionalL2 P hm f‖ ≤ ‖f‖ := norm_condExpL2_coe_le hm f

theorem conditionalL2_ae (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (f : Lp ℝ 2 P) :
    (conditionalL2 P hm f : Ω → ℝ) =ᵐ[P] P[f | m] := by
  have h := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℝ) hm
  simpa only [Lp.toLp_coeFn] using h

theorem conditionalL2_toLp (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (f : Ω → ℝ) (hf : MemLp f 2 P) :
    conditionalL2 P hm (hf.toLp f) = hf.condExp.toLp (P[f | m]) := by
  apply Lp.ext
  exact ((conditionalL2_ae P hm (hf.toLp f)).trans
    (condExp_congr_ae hf.coeFn_toLp)).trans hf.condExp.coeFn_toLp.symm

theorem conditionalL2_fixed (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (f : Lp ℝ 2 P) (hf : AEStronglyMeasurable[m] f P) :
    conditionalL2 P hm f = f := by
  apply Lp.ext
  exact (conditionalL2_ae P hm f).trans
    (condExp_of_aestronglyMeasurable' hm hf ((Lp.memLp f).integrable (by norm_num)))

theorem conditionalL2_tower (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ mΩ) (f : Lp ℝ 2 P) :
    conditionalL2 P (h₁₂.trans h₂) (conditionalL2 P h₂ f) =
      conditionalL2 P (h₁₂.trans h₂) f := by
  apply Lp.ext
  exact ((conditionalL2_ae P (h₁₂.trans h₂) (conditionalL2 P h₂ f)).trans
    ((condExp_congr_ae (conditionalL2_ae P h₂ f)).trans
      (condExp_condExp_of_le h₁₂ h₂))).trans (conditionalL2_ae P (h₁₂.trans h₂) f).symm

theorem conditionalL2_zero_condExp (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (f : Lp ℝ 2 P) (hf : conditionalL2 P hm f = 0) :
    P[f | m] =ᵐ[P] 0 := by
  have h := (conditionalL2_ae P hm f).symm
  rw [hf] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 P)

theorem condExp_abs_le (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (f : Ω → ℝ) (hf : Integrable f P) (B : ℝ)
    (hB : ∀ᵐ ω ∂P, |f ω| ≤ B) : ∀ᵐ ω ∂P, |(P[f | m]) ω| ≤ B := by
  have hlo : (fun _ : Ω => -B) ≤ᵐ[P] f := hB.mono fun _ h => (abs_le.mp h).1
  have hhi : f ≤ᵐ[P] (fun _ : Ω => B) := hB.mono fun _ h => (abs_le.mp h).2
  have h₁ := condExp_mono (m := m) (integrable_const (-B)) hf hlo
  have h₂ := condExp_mono (m := m) hf (integrable_const B) hhi
  rw [condExp_const hm (-B)] at h₁
  rw [condExp_const hm B] at h₂
  filter_upwards [h₁, h₂] with ω h₁ h₂ using abs_le.mpr ⟨h₁, h₂⟩

theorem conditionalL2_abs_le (P : @Measure Ω mΩ) [IsFiniteMeasure P]
    (hm : m ≤ mΩ) (f : Lp ℝ 2 P) (B : ℝ) (hB : ∀ᵐ ω ∂P, |f ω| ≤ B) :
    ∀ᵐ ω ∂P, |conditionalL2 P hm f ω| ≤ B := by
  filter_upwards [conditionalL2_ae P hm f,
    condExp_abs_le P hm f ((Lp.memLp f).integrable (by norm_num)) B hB] with ω hω hbound
  simpa [hω] using hbound

theorem conditionalL2_norm_le_rho (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (n k : ℕ) (V : Ω → ℝ)
    (hVm : Measurable[processSigma Y (Set.Ici (n + k))] V)
    (hV : MemLp V 2 P) (hcent : ∫ ω, V ω ∂P = 0) :
    ‖conditionalL2 P ((naturalFiltration Y hY).le n) (hV.toLp V)‖ ≤
      rhoMixingCoef P Y k * ‖hV.toLp V‖ := by
  rw [conditionalL2_toLp]
  exact condExp_norm_le_rho P Y hY n k V hVm hV hcent

end SummableRhoUI

end UIComponent3

section UIComponent4

/- The path-law pushforward argument below lifts the coordinate-law and L2
transfer steps in Gabewhigham's accepted covariance proof
a1cb1e12-f123-4e20-92be-d71f233bbe7b (full original captured in dependencies/).
The public truncation theorem is used with its full accepted proof mirror. -/

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem stationary_coordinate_law (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y) (k : ℕ) :
    P.map (Y k) = P.map (Y 0) := by
  have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
  rw [Measure.map_map (measurable_pi_apply 0)
      (measurable_pi_lambda _ fun n => hY (n + k)),
    Measure.map_map (measurable_pi_apply 0)
      (measurable_pi_lambda _ fun n => hY n)] at h
  simpa [Function.comp_def] using h

theorem stationary_integral_comp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (g : ℝ → ℝ) (hg : Measurable g) (k : ℕ) :
    ∫ ω, g (Y k ω) ∂P = ∫ ω, g (Y 0 ω) ∂P := by
  rw [← integral_map (hY k).aemeasurable hg.aestronglyMeasurable,
    stationary_coordinate_law P Y hY hstat k,
    integral_map (hY 0).aemeasurable hg.aestronglyMeasurable]

theorem stationary_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (k : ℕ) : MemLp (Y k) 2 P := by
  have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
    (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hY 0).aemeasurable).2 hL2
  have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by
    rw [stationary_coordinate_law P Y hY hstat k]
    exact h0
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable (hY k).aemeasurable).1 hk

noncomputable def stationaryLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) : Lp ℝ 2 P :=
  (stationary_memLp P Y hY hstat hL2 n).toLp (Y n)

theorem stationaryLp_ae (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    (stationaryLp P Y hY hstat hL2 n : Ω → ℝ) =ᵐ[P] Y n := MemLp.coeFn_toLp _

theorem stationaryLp_norm (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    ‖stationaryLp P Y hY hstat hL2 n‖ = ‖hL2.toLp (Y 0)‖ := by
  have hn := norm_toLp_sq_integral P (Y n) (stationary_memLp P Y hY hstat hL2 n)
  have h0 := norm_toLp_sq_integral P (Y 0) hL2
  have he := stationary_integral_comp P Y hY hstat (fun x => x ^ 2) (by fun_prop) n
  change ‖(stationary_memLp P Y hY hstat hL2 n).toLp (Y n)‖ = _
  nlinarith [norm_nonneg ((stationary_memLp P Y hY hstat hL2 n).toLp (Y n)),
    norm_nonneg (hL2.toLp (Y 0))]

omit mΩ in
theorem coordinate_measurable_past (Y : ℕ → Ω → ℝ) (i n : ℕ) (hi : i ≤ n) :
    Measurable[processSigma Y (Set.Iic n)] (Y i) := by
  refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
  exact le_iSup₂ (f := fun j (_ : j ∈ Set.Iic n) =>
    MeasurableSpace.comap (Y j) inferInstance) i hi

omit mΩ in
theorem coordinate_measurable_future (Y : ℕ → Ω → ℝ) (i n : ℕ) (hi : n ≤ i) :
    Measurable[processSigma Y (Set.Ici n)] (Y i) := by
  refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
  exact le_iSup₂ (f := fun j (_ : j ∈ Set.Ici n) =>
    MeasurableSpace.comap (Y j) inferInstance) i hi

theorem stationaryLp_adapted (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    AEStronglyMeasurable[naturalFiltration Y hY n]
      (stationaryLp P Y hY hstat hL2 n) P := by
  exact (coordinate_measurable_past Y n n le_rfl).stronglyMeasurable.aestronglyMeasurable.congr
    (stationaryLp_ae P Y hY hstat hL2 n).symm

def clip (K : ℝ) (x : ℝ) : ℝ := max (min x K) (-K)

theorem abs_clip_le (K : ℝ) (hK : 0 ≤ K) (x : ℝ) : |clip K x| ≤ K := by
  apply abs_le.mpr
  constructor
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (by linarith)

theorem stationary_clip_error (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hstat : IsStrictlyStationary P Y) (K : ℝ) (n : ℕ) :
    ∫ ω, (Y n ω - clip K (Y n ω)) ^ 2 ∂P =
      ∫ ω, (Y 0 ω - clip K (Y 0 ω)) ^ 2 ∂P := by
  exact stationary_integral_comp P Y hY hstat (fun x => (x - clip K x) ^ 2)
    (by unfold clip; fun_prop) n

theorem tendsto_stationary_clip_error (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hL2 : MemLp (Y 0) 2 P) :
    Tendsto (fun K : ℕ => ∫ ω, (Y 0 ω - clip K (Y 0 ω)) ^ 2 ∂P) atTop (𝓝 0) :=
  tendsto_integral_sq_sub_truncation P (Y 0) (hY 0) hL2.integrable_sq

end SummableRhoUI

end UIComponent4

section UIComponent5

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem stationaryLp_bounded_approximation (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (B : ℝ) (_ : 0 ≤ B) (w : ℕ → Lp ℝ 2 P),
      (∀ n, AEStronglyMeasurable[naturalFiltration Y hY n] (w n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |w n ω| ≤ B) ∧
      ∀ n, ‖stationaryLp P Y hY hstat hL2 n - w n‖ ≤ δ := by
  have he := (tendsto_stationary_clip_error P Y hY hL2).eventually
    (gt_mem_nhds (sq_pos_of_pos hδ))
  obtain ⟨K, hK⟩ := he.exists
  have hm : ∀ n, Measurable[naturalFiltration Y hY n] (fun ω => clip K (Y n ω)) := by
    intro n
    unfold clip
    exact ((coordinate_measurable_past Y n n le_rfl).min measurable_const).max measurable_const
  have hw : ∀ n, MemLp (fun ω => clip K (Y n ω)) 2 P := by
    intro n
    apply MemLp.of_bound (((hm n).mono ((naturalFiltration Y hY).le n) le_rfl).aestronglyMeasurable)
      (K : ℝ)
    exact Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using abs_clip_le (K : ℝ) (Nat.cast_nonneg K) (Y n ω)
  let w : ℕ → Lp ℝ 2 P := fun n => (hw n).toLp (fun ω => clip K (Y n ω))
  refine ⟨K, Nat.cast_nonneg K, w, ?_, ?_, ?_⟩
  · intro n
    exact (hm n).stronglyMeasurable.aestronglyMeasurable.congr (hw n).coeFn_toLp.symm
  · intro n
    filter_upwards [(hw n).coeFn_toLp] with ω hω
    rw [show w n ω = clip K (Y n ω) from hω]
    exact abs_clip_le K (Nat.cast_nonneg K) (Y n ω)
  · intro n
    have hs := norm_toLp_sq_integral P (fun ω => Y n ω - clip K (Y n ω))
      ((stationary_memLp P Y hY hstat hL2 n).sub (hw n))
    change ‖stationaryLp P Y hY hstat hL2 n - w n‖ ^ 2 = _ at hs
    rw [stationary_clip_error P Y hY hstat K n] at hs
    nlinarith [norm_nonneg (stationaryLp P Y hY hstat hL2 n - w n)]

end SummableRhoUI

end UIComponent5

section UIComponent6

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

noncomputable def projectiveTail (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (n : ℕ) : Lp ℝ 2 P :=
  ∑' k, conditionalL2 P (F.le n) (x (n + k + 1))

noncomputable def projectiveIncrement (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (n : ℕ) : Lp ℝ 2 P :=
  x (n + 1) + projectiveTail P F x (n + 1) - projectiveTail P F x n

theorem projective_summable (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k) (n : ℕ) :
    Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1))) :=
  ha.of_norm_bounded (hbound n)

theorem projectiveTail_norm_le (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k) (n : ℕ) :
    ‖projectiveTail P F x n‖ ≤ ∑' k, a k := by
  have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg
    (conditionalL2 P (F.le n) (x (n + k + 1)))) (hbound n) ha
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (hbound n) ha)

theorem projectiveTail_fixed (P : Measure Ω) [IsFiniteMeasure P] (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P)
    (hs : ∀ n, Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1)))) (n : ℕ) :
    conditionalL2 P (F.le n) (projectiveTail P F x n) = projectiveTail P F x n := by
  unfold projectiveTail
  rw [(conditionalL2 P (F.le n)).map_tsum (hs n)]
  apply tsum_congr
  intro k
  exact conditionalL2_tower P le_rfl (F.le n) (x (n + k + 1))

theorem projectiveTail_adapted (P : Measure Ω) [IsFiniteMeasure P] (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P)
    (hs : ∀ n, Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1)))) (n : ℕ) :
    AEStronglyMeasurable[F n] (projectiveTail P F x n) P := by
  rw [← projectiveTail_fixed P F x hs n]
  exact conditionalL2_adapted P (F.le n) _

theorem projectiveTail_tower (P : Measure Ω) [IsFiniteMeasure P] (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P)
    (hs : ∀ n, Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1)))) (n : ℕ) :
    conditionalL2 P (F.le n) (x (n + 1) + projectiveTail P F x (n + 1)) =
      projectiveTail P F x n := by
  rw [map_add]
  unfold projectiveTail
  rw [(conditionalL2 P (F.le n)).map_tsum (hs (n + 1)), (hs n).tsum_eq_zero_add]
  congr 1
  apply tsum_congr
  intro k
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    conditionalL2_tower P (F.mono (Nat.le_succ n)) (F.le (n + 1)) (x (n + 1 + k + 1))

theorem projectiveIncrement_projection_zero (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (x : ℕ → Lp ℝ 2 P)
    (hs : ∀ n, Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1)))) (n : ℕ) :
    conditionalL2 P (F.le n) (projectiveIncrement P F x n) = 0 := by
  unfold projectiveIncrement
  rw [map_sub, projectiveTail_tower P F x hs n, projectiveTail_fixed P F x hs n, sub_self]

theorem projectiveIncrement_condExp_zero (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (x : ℕ → Lp ℝ 2 P)
    (hs : ∀ n, Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1)))) (n : ℕ) :
    P[(projectiveIncrement P F x n : Ω → ℝ) | F n] =ᵐ[P] 0 :=
  conditionalL2_zero_condExp P (F.le n) _ (projectiveIncrement_projection_zero P F x hs n)

theorem projectiveIncrement_adapted (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (x : ℕ → Lp ℝ 2 P)
    (hx : ∀ n, AEStronglyMeasurable[F n] (x n) P)
    (hs : ∀ n, Summable (fun k => conditionalL2 P (F.le n) (x (n + k + 1)))) (n : ℕ) :
    AEStronglyMeasurable[F (n + 1)] (projectiveIncrement P F x n) P := by
  have hfix : conditionalL2 P (F.le (n + 1)) (projectiveIncrement P F x n) =
      projectiveIncrement P F x n := by
    unfold projectiveIncrement
    rw [map_sub, map_add, conditionalL2_fixed P (F.le (n + 1)) (x (n + 1)) (hx (n + 1)),
      projectiveTail_fixed P F x hs (n + 1),
      conditionalL2_fixed P (F.le (n + 1)) (projectiveTail P F x n)
        ((projectiveTail_adapted P F x hs n).mono (F.mono (Nat.le_succ n)))]
  rw [← hfix]
  exact conditionalL2_adapted P (F.le (n + 1)) _

theorem projective_sum_telescope (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (n : ℕ) :
    ∑ i ∈ Finset.range n, projectiveIncrement P F x i =
      (∑ i ∈ Finset.range n, x (i + 1)) + projectiveTail P F x n - projectiveTail P F x 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    unfold projectiveIncrement
    abel

theorem partialSum_projective (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), x i =
      (∑ i ∈ Finset.range n, projectiveIncrement P F x i) +
        x 0 + projectiveTail P F x 0 - projectiveTail P F x n := by
  rw [projective_sum_telescope, Finset.sum_range_succ']
  abel

noncomputable def projectiveApprox (P : Measure Ω) (F : Filtration ℕ mΩ)
    (w : ℕ → Lp ℝ 2 P) (L n : ℕ) : Lp ℝ 2 P :=
  ∑ k ∈ Finset.range L, conditionalL2 P (F.le n) (w (n + k + 1))

theorem projectiveApprox_adapted (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (w : ℕ → Lp ℝ 2 P) (L n : ℕ) :
    AEStronglyMeasurable[F n] (projectiveApprox P F w L n) P := by
  have hfix : conditionalL2 P (F.le n) (projectiveApprox P F w L n) =
      projectiveApprox P F w L n := by
    unfold projectiveApprox
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact conditionalL2_tower P le_rfl (F.le n) _
  rw [← hfix]
  exact conditionalL2_adapted P (F.le n) _

theorem projectiveTail_sub_finite_norm (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k) (L n : ℕ) :
    ‖projectiveTail P F x n - projectiveApprox P F x L n‖ ≤ ∑' k, a (k + L) := by
  have hs := projective_summable P F x a ha hbound n
  have he := hs.sum_add_tsum_nat_add L
  have hsub : projectiveTail P F x n - projectiveApprox P F x L n =
      ∑' k, conditionalL2 P (F.le n) (x (n + (k + L) + 1)) := by
    unfold projectiveTail projectiveApprox
    rw [← he]
    abel
  rw [hsub]
  have ha' : Summable (fun k => a (k + L)) := (summable_nat_add_iff L).2 ha
  have hn := Summable.of_nonneg_of_le (fun k => norm_nonneg
    (conditionalL2 P (F.le n) (x (n + (k + L) + 1)))) (fun k => hbound n (k + L)) ha'
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun k => hbound n (k + L)) ha')

theorem projectiveApprox_sub_norm (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x w : ℕ → Lp ℝ 2 P) (δ : ℝ) (hδ : ∀ i, ‖x i - w i‖ ≤ δ) (L n : ℕ) :
    ‖projectiveApprox P F x L n - projectiveApprox P F w L n‖ ≤ (L : ℝ) * δ := by
  unfold projectiveApprox
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ k ∈ Finset.range L, (conditionalL2 P (F.le n) (x (n + k + 1)) -
        conditionalL2 P (F.le n) (w (n + k + 1)))‖ ≤
        ∑ k ∈ Finset.range L, ‖conditionalL2 P (F.le n) (x (n + k + 1)) -
          conditionalL2 P (F.le n) (w (n + k + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range L, δ := by
      apply Finset.sum_le_sum
      intro k _
      rw [← map_sub]
      exact (conditionalL2_norm_le P (F.le n) _).trans (hδ _)
    _ = (L : ℝ) * δ := by simp

theorem projectiveTail_approx_norm (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x w : ℕ → Lp ℝ 2 P) (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k)
    (δ : ℝ) (hδ : ∀ i, ‖x i - w i‖ ≤ δ) (L n : ℕ) :
    ‖projectiveTail P F x n - projectiveApprox P F w L n‖ ≤
      (∑' k, a (k + L)) + (L : ℝ) * δ := by
  calc
    ‖projectiveTail P F x n - projectiveApprox P F w L n‖ ≤
        ‖projectiveTail P F x n - projectiveApprox P F x L n‖ +
          ‖projectiveApprox P F x L n - projectiveApprox P F w L n‖ := by
      simpa only [dist_eq_norm] using dist_triangle (projectiveTail P F x n)
        (projectiveApprox P F x L n) (projectiveApprox P F w L n)
    _ ≤ _ := add_le_add (projectiveTail_sub_finite_norm P F x a ha hbound L n)
      (projectiveApprox_sub_norm P F x w δ hδ L n)

end SummableRhoUI

end UIComponent6

section UIComponent7

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem projective_lp_sum_ae {ι : Type*} (P : Measure Ω) (s : Finset ι)
    (f : ι → Lp ℝ 2 P) :
    ((∑ i ∈ s, f i : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω => ∑ i ∈ s, f i ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℝ 2 P
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with ω hadd hsum
    exact hadd.trans (congrArg (fun v : ℝ => f i ω + v) hsum)

theorem projectiveApprox_abs_le (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (w : ℕ → Lp ℝ 2 P) (B : ℝ)
    (hB : ∀ i, ∀ᵐ ω ∂P, |w i ω| ≤ B) (L n : ℕ) :
    ∀ᵐ ω ∂P, |projectiveApprox P F w L n ω| ≤ (L : ℝ) * B := by
  have hb : ∀ᵐ ω ∂P, ∀ k : ℕ, |conditionalL2 P (F.le n) (w (n + k + 1)) ω| ≤ B :=
    ae_all_iff.mpr fun k => conditionalL2_abs_le P (F.le n) _ B (hB _)
  filter_upwards [projective_lp_sum_ae P (Finset.range L)
    (fun k => conditionalL2 P (F.le n) (w (n + k + 1))), hb] with ω he hb
  unfold projectiveApprox
  rw [he]
  calc
    |∑ k ∈ Finset.range L, conditionalL2 P (F.le n) (w (n + k + 1)) ω| ≤
        ∑ k ∈ Finset.range L, |conditionalL2 P (F.le n) (w (n + k + 1)) ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range L, B := Finset.sum_le_sum fun k _ => hb k
    _ = (L : ℝ) * B := by simp

noncomputable def projectiveIncrementApprox (P : Measure Ω) (F : Filtration ℕ mΩ)
    (w : ℕ → Lp ℝ 2 P) (L n : ℕ) : Lp ℝ 2 P :=
  w (n + 1) + projectiveApprox P F w L (n + 1) - projectiveApprox P F w L n

theorem projectiveIncrementApprox_adapted (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (w : ℕ → Lp ℝ 2 P)
    (hw : ∀ n, AEStronglyMeasurable[F n] (w n) P) (L n : ℕ) :
    AEStronglyMeasurable[F (n + 1)] (projectiveIncrementApprox P F w L n) P := by
  have hfix : conditionalL2 P (F.le (n + 1)) (projectiveIncrementApprox P F w L n) =
      projectiveIncrementApprox P F w L n := by
    unfold projectiveIncrementApprox
    rw [map_sub, map_add,
      conditionalL2_fixed P (F.le (n + 1)) (w (n + 1)) (hw (n + 1)),
      conditionalL2_fixed P (F.le (n + 1)) (projectiveApprox P F w L (n + 1))
        (projectiveApprox_adapted P F w L (n + 1)),
      conditionalL2_fixed P (F.le (n + 1)) (projectiveApprox P F w L n)
        ((projectiveApprox_adapted P F w L n).mono (F.mono (Nat.le_succ n)))]
  rw [← hfix]
  exact conditionalL2_adapted P (F.le (n + 1)) _

theorem projectiveIncrementApprox_abs_le (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (w : ℕ → Lp ℝ 2 P) (B : ℝ)
    (hB : ∀ i, ∀ᵐ ω ∂P, |w i ω| ≤ B) (L n : ℕ) :
    ∀ᵐ ω ∂P, |projectiveIncrementApprox P F w L n ω| ≤ (2 * (L : ℝ) + 1) * B := by
  filter_upwards [Lp.coeFn_sub (w (n + 1) + projectiveApprox P F w L (n + 1))
    (projectiveApprox P F w L n),
    Lp.coeFn_add (w (n + 1)) (projectiveApprox P F w L (n + 1)),
    hB (n + 1), projectiveApprox_abs_le P F w B hB L (n + 1),
    projectiveApprox_abs_le P F w B hB L n] with ω hsub hadd hw hp hn
  change |(w (n + 1) + projectiveApprox P F w L (n + 1) - projectiveApprox P F w L n) ω| ≤ _
  rw [hsub, Pi.sub_apply, hadd, Pi.add_apply]
  have h₁ := abs_sub (w (n + 1) ω + projectiveApprox P F w L (n + 1) ω)
    (projectiveApprox P F w L n ω)
  have h₂ := abs_add_le (w (n + 1) ω) (projectiveApprox P F w L (n + 1) ω)
  nlinarith

theorem projectiveIncrement_approx_norm (P : Measure Ω) (F : Filtration ℕ mΩ)
    (x w : ℕ → Lp ℝ 2 P) (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k)
    (δ : ℝ) (hδ : ∀ i, ‖x i - w i‖ ≤ δ) (L n : ℕ) :
    ‖projectiveIncrement P F x n - projectiveIncrementApprox P F w L n‖ ≤
      2 * (∑' k, a (k + L)) + (2 * (L : ℝ) + 1) * δ := by
  have he : projectiveIncrement P F x n - projectiveIncrementApprox P F w L n =
      (x (n + 1) - w (n + 1)) +
        (projectiveTail P F x (n + 1) - projectiveApprox P F w L (n + 1)) -
        (projectiveTail P F x n - projectiveApprox P F w L n) := by
    unfold projectiveIncrement projectiveIncrementApprox
    abel
  rw [he]
  have h₁ := norm_sub_le
    ((x (n + 1) - w (n + 1)) +
      (projectiveTail P F x (n + 1) - projectiveApprox P F w L (n + 1)))
    (projectiveTail P F x n - projectiveApprox P F w L n)
  have h₂ := norm_add_le (x (n + 1) - w (n + 1))
    (projectiveTail P F x (n + 1) - projectiveApprox P F w L (n + 1))
  have h₃ := projectiveTail_approx_norm P F x w a ha hbound δ hδ L (n + 1)
  have h₄ := projectiveTail_approx_norm P F x w a ha hbound δ hδ L n
  have h₅ := hδ (n + 1)
  nlinarith

theorem projectiveIncrement_bounded_approximation (P : Measure Ω) [IsFiniteMeasure P]
    (F : Filtration ℕ mΩ) (x : ℕ → Lp ℝ 2 P) (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ (B : ℝ) (_ : 0 ≤ B) (w : ℕ → Lp ℝ 2 P),
      (∀ n, AEStronglyMeasurable[F n] (w n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |w n ω| ≤ B) ∧ ∀ n, ‖x n - w n‖ ≤ δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (W : ℕ → Ω → ℝ),
      (∀ n, AEStronglyMeasurable[F (n + 1)] (W n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ C) ∧
      ∀ n, eLpNorm (fun ω => projectiveIncrement P F x n ω - W n ω) 2 P ≤ ENNReal.ofReal ε := by
  have ht := (tendsto_sum_nat_add a).eventually (gt_mem_nhds (show 0 < ε / 4 by positivity))
  obtain ⟨L, hL⟩ := ht.exists
  let δ : ℝ := ε / (2 * (2 * (L : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, w, hw, hwb, hwd⟩ := happrox δ hδ
  let C : ℝ := (2 * (L : ℝ) + 1) * B
  let W : ℕ → Ω → ℝ := fun n => projectiveIncrementApprox P F w L n
  refine ⟨C, by dsimp [C]; positivity, W,
    fun n => projectiveIncrementApprox_adapted P F w hw L n,
    fun n => projectiveIncrementApprox_abs_le P F w B hwb L n, ?_⟩
  intro n
  have hd : (2 * (L : ℝ) + 1) * δ = ε / 2 := by
    dsimp [δ]
    field_simp
  have hn := projectiveIncrement_approx_norm P F x w a ha hbound δ hwd L n
  rw [hd] at hn
  have hn' : ‖projectiveIncrement P F x n - projectiveIncrementApprox P F w L n‖ ≤ ε := by
    linarith
  change eLpNorm (fun ω => projectiveIncrement P F x n ω - projectiveIncrementApprox P F w L n ω)
    2 P ≤ _
  have he : eLpNorm (fun ω => projectiveIncrement P F x n ω - projectiveIncrementApprox P F w L n ω)
      2 P = ENNReal.ofReal ‖projectiveIncrement P F x n - projectiveIncrementApprox P F w L n‖ := by
    exact (eLpNorm_congr_ae (p := 2) (Lp.coeFn_sub (projectiveIncrement P F x n)
      (projectiveIncrementApprox P F w L n))).symm.trans (by rw [← Lp.enorm_def, ofReal_norm])
  rw [he]
  exact ENNReal.ofReal_le_ofReal hn'

end SummableRhoUI

end UIComponent7

section UIComponent8

open MeasureTheory
open scoped ENNReal NNReal

namespace SummableRhoUI

/- The following complete FourthRecurrence namespace is retained verbatim from
ryanshin's accepted submission b434e964-c658-411b-ab9f-bcba879ef869 for theorem
5909e9db-042a-4d8a-8050-d16e7bec2e97. Original source SHA256:
4feb5e7528ab36453533dc6816954ffb736c4e6ba2684769f71e4e5eed454629.
The selected byte interval [670,6847) has SHA256:
08903a629552b23fbbbcb9380353c959b5ace1bdabfb10c38847cd1b9c37ed92.
Only this enclosing namespace and focused imports are new. -/

namespace FourthRecurrence

variable {Ω : Type*} [MeasurableSpace Ω]

def partialSum (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, D k ω

omit [MeasurableSpace Ω] in
theorem partialSum_zero (D : ℕ → Ω → ℝ) (ω : Ω) : partialSum D 0 ω = 0 := by
  simp [partialSum]

omit [MeasurableSpace Ω] in
theorem partialSum_succ (D : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    partialSum D (n + 1) ω = partialSum D n ω + D n ω := by
  simp [partialSum, Finset.sum_range_succ]

theorem measurable_partialSum (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (n : ℕ) :
    Measurable (partialSum D n) := by
  unfold partialSum
  exact Finset.measurable_sum _ (fun n _ => hD n)

omit [MeasurableSpace Ω] in
theorem partialSum_bound (D : ℕ → Ω → ℝ) (c : ℝ)
    (hbound : ∀ n ω, |D n ω| ≤ c) (n : ℕ) (ω : Ω) :
    |partialSum D n ω| ≤ (n : ℝ) * c := by
  unfold partialSum
  calc
    |∑ k ∈ Finset.range n, D k ω| ≤ ∑ k ∈ Finset.range n, |D k ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, c := Finset.sum_le_sum (fun k _ => hbound k ω)
    _ = (n : ℝ) * c := by simp

theorem integrable_monomial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n ω, |D n ω| ≤ c) (n p q : ℕ) :
    Integrable (fun ω => partialSum D n ω ^ p * D n ω ^ q) μ := by
  apply Integrable.of_bound
    (((measurable_partialSum D hD n).pow_const p).mul ((hD n).pow_const q)).aestronglyMeasurable
    (((n : ℝ) * c) ^ p * c ^ q)
  apply Filter.Eventually.of_forall
  intro ω
  simp only [norm_mul, norm_pow, Real.norm_eq_abs]
  exact mul_le_mul
    (pow_le_pow_left₀ (abs_nonneg _) (partialSum_bound D c hbound n ω) p)
    (pow_le_pow_left₀ (abs_nonneg _) (hbound n ω) q)
    (by positivity) (by positivity)

theorem integrable_fourth (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n ω, |D n ω| ≤ c) (n : ℕ) :
    Integrable (fun ω => partialSum D n ω ^ 4) μ := by
  simpa only [pow_zero, mul_one] using integrable_monomial μ D hD c hc hbound n 4 0

theorem fourth_step_bound (m d c t : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ t)
    (hm : |m| ≤ t * c) (hd : |d| ≤ c) :
    (m + d) ^ 4 ≤ m ^ 4 + 4 * (m ^ 3 * d) +
      6 * c ^ 2 * m ^ 2 + (4 * t + 1) * c ^ 4 := by
  have hd2 : d ^ 2 ≤ c ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hd4 : d ^ 4 ≤ c ^ 4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg d) hd2 2
  have hmd3 : m * d ^ 3 ≤ t * c ^ 4 := by
    calc
      m * d ^ 3 ≤ |m * d ^ 3| := le_abs_self _
      _ = |m| * |d| ^ 3 := by rw [abs_mul, abs_pow]
      _ ≤ (t * c) * c ^ 3 :=
        mul_le_mul hm (pow_le_pow_left₀ (abs_nonneg d) hd 3) (by positivity) (by positivity)
      _ = t * c ^ 4 := by ring
  have hmd2 : m ^ 2 * d ^ 2 ≤ c ^ 2 * m ^ 2 := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hd2 (sq_nonneg m)
  nlinarith

theorem integral_fourth_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : ℕ → Ω → ℝ) (hD : ∀ n, Measurable (D n)) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ n ω, |D n ω| ≤ c)
    (horth : ∀ n, ∫ ω, partialSum D n ω ^ 3 * D n ω ∂μ = 0)
    (hsecond : ∀ n, (∫ ω, partialSum D n ω ^ 2 ∂μ) ≤ (n : ℝ) * c ^ 2)
    (n : ℕ) :
    (∫ ω, partialSum D n ω ^ 4 ∂μ) ≤ 6 * c ^ 4 * (n : ℝ) ^ 2 := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      have hi4 := integrable_fourth μ D hD c hc hbound n
      have hi3 : Integrable (fun ω => partialSum D n ω ^ 3 * D n ω) μ := by
        simpa only [pow_one] using integrable_monomial μ D hD c hc hbound n 3 1
      have hi2 : Integrable (fun ω => partialSum D n ω ^ 2) μ := by
        simpa only [pow_zero, mul_one] using integrable_monomial μ D hD c hc hbound n 2 0
      have hstep : (∫ ω, partialSum D (n + 1) ω ^ 4 ∂μ) ≤
          (∫ ω, partialSum D n ω ^ 4 ∂μ) +
          6 * c ^ 2 * (∫ ω, partialSum D n ω ^ 2 ∂μ) +
          (4 * (n : ℝ) + 1) * c ^ 4 := by
        calc
          (∫ ω, partialSum D (n + 1) ω ^ 4 ∂μ) ≤
              ∫ ω, partialSum D n ω ^ 4 + 4 * (partialSum D n ω ^ 3 * D n ω) +
                (6 * c ^ 2) * partialSum D n ω ^ 2 + (4 * (n : ℝ) + 1) * c ^ 4 ∂μ := by
            apply integral_mono (integrable_fourth μ D hD c hc hbound (n + 1))
              (((hi4.add (hi3.const_mul 4)).add (hi2.const_mul (6 * c ^ 2))).add
                (integrable_const ((4 * (n : ℝ) + 1) * c ^ 4)))
            intro ω
            dsimp only [Pi.add_apply]
            rw [partialSum_succ]
            exact fourth_step_bound _ _ c n hc (Nat.cast_nonneg n)
              (partialSum_bound D c hbound n ω) (hbound n ω)
          _ = _ := by
            rw [integral_add
                (f := fun ω => partialSum D n ω ^ 4 + 4 * (partialSum D n ω ^ 3 * D n ω) +
                  (6 * c ^ 2) * partialSum D n ω ^ 2)
                (g := fun _ => (4 * (n : ℝ) + 1) * c ^ 4)
                ((hi4.add (hi3.const_mul 4)).add (hi2.const_mul (6 * c ^ 2)))
                (integrable_const ((4 * (n : ℝ) + 1) * c ^ 4)),
              integral_add
                (f := fun ω => partialSum D n ω ^ 4 + 4 * (partialSum D n ω ^ 3 * D n ω))
                (g := fun ω => (6 * c ^ 2) * partialSum D n ω ^ 2)
                (hi4.add (hi3.const_mul 4)) (hi2.const_mul (6 * c ^ 2)),
              integral_add (f := fun ω => partialSum D n ω ^ 4)
                (g := fun ω => 4 * (partialSum D n ω ^ 3 * D n ω)) hi4 (hi3.const_mul 4)]
            simp only [integral_const_mul, integral_const, horth n, mul_zero, add_zero,
              probReal_univ, smul_eq_mul, one_mul]
      have hsecond' := mul_le_mul_of_nonneg_left (hsecond n) (by positivity : 0 ≤ 6 * c ^ 2)
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hc4 : 0 ≤ c ^ 4 := by positivity
      push_cast
      nlinarith

end FourthRecurrence

abbrev mdsSum {Ω : Type*} (D : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  FourthRecurrence.partialSum D n

noncomputable def normalizedMdsSum {Ω : Type*} (D : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : ℝ := mdsSum D n ω / Real.sqrt ((n : ℝ) + 1)

section

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

lemma integral_mul_eq_zero_of_condExp (P : Measure Ω) [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ m0) {U D : Ω → ℝ}
    (hU : AEStronglyMeasurable[m] U P) (hUD : Integrable (U * D) P)
    (hD : Integrable D P) (hzero : P[D | m] =ᵐ[P] 0) :
    (∫ ω, U ω * D ω ∂P) = 0 := by
  haveI : IsFiniteMeasure (P.trim hm) := isFiniteMeasure_trim hm
  have hpull := condExp_mul_of_aestronglyMeasurable_left hU hUD hD
  calc
    (∫ ω, U ω * D ω ∂P) = ∫ ω, (P[U * D | m]) ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ ω, U ω * (P[D | m]) ω ∂P := integral_congr_ae hpull
    _ = 0 := by
      calc
        _ = ∫ _ω : Ω, (0 : ℝ) ∂P := by
          apply integral_congr_ae
          filter_upwards [hzero] with ω hω
          simp only [hω, Pi.zero_apply, mul_zero]
        _ = 0 := by simp

lemma mdsSum_aestronglyMeasurable_past (P : Measure Ω) (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P) (n : ℕ) :
    AEStronglyMeasurable[F n] (mdsSum D n) P := by
  let G : ℕ → Ω → ℝ := fun i => (hD i).mk (D i)
  have hG : Measurable[F n] (fun ω => ∑ i ∈ Finset.range n, G i ω) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((hD i).stronglyMeasurable_mk.mono
      (F.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))).measurable
  refine ⟨_, hG.stronglyMeasurable, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => (hD i).ae_eq_mk)] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

lemma memLp_mdsSum (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, MemLp (D n) 2 P) (n : ℕ) : MemLp (mdsSum D n) 2 P :=
  memLp_finsetSum (Finset.range n) (fun i _ => hD i)

lemma memLp_normalizedMdsSum (P : Measure Ω) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, MemLp (D n) 2 P) (n : ℕ) : MemLp (normalizedMdsSum D n) 2 P := by
  simpa only [normalizedMdsSum, div_eq_mul_inv] using
    (memLp_mdsSum P D hD n).mul_const (Real.sqrt ((n : ℝ) + 1))⁻¹

theorem integral_mdsSum_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    (∫ ω, mdsSum D n ω ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, D i ω ^ 2 ∂P := by
  induction n with
  | zero => simp [mdsSum, FourthRecurrence.partialSum]
  | succ n ih =>
      have hM := memLp_mdsSum P D hL2 n
      have hiM : Integrable (fun ω => mdsSum D n ω ^ 2) P :=
        (memLp_two_iff_integrable_sq hM.1).mp hM
      have hiD : Integrable (fun ω => D n ω ^ 2) P :=
        (memLp_two_iff_integrable_sq (hL2 n).1).mp (hL2 n)
      have hiMD : Integrable (fun ω => mdsSum D n ω * D n ω) P :=
        hM.integrable_mul (hL2 n)
      have hMD : (∫ ω, mdsSum D n ω * D n ω ∂P) = 0 :=
        integral_mul_eq_zero_of_condExp P (F.le n)
          (mdsSum_aestronglyMeasurable_past P F D hD n) hiMD
          ((hL2 n).integrable (by norm_num)) (hzero n)
      have hpoly : (fun ω => mdsSum D (n + 1) ω ^ 2) =
          (fun ω => mdsSum D n ω ^ 2 + 2 * (mdsSum D n ω * D n ω) + D n ω ^ 2) := by
        funext ω
        simp only [mdsSum, FourthRecurrence.partialSum_succ]
        ring
      rw [hpoly, integral_add
          (f := fun ω => mdsSum D n ω ^ 2 + 2 * (mdsSum D n ω * D n ω))
          (g := fun ω => D n ω ^ 2) (hiM.add (hiMD.const_mul 2)) hiD,
        integral_add (f := fun ω => mdsSum D n ω ^ 2)
          (g := fun ω => 2 * (mdsSum D n ω * D n ω)) hiM (hiMD.const_mul 2),
        integral_const_mul, hMD,
        mul_zero, add_zero, ih, Finset.sum_range_succ]

theorem integral_normalizedMdsSum_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    (∫ ω, normalizedMdsSum D n ω ^ 2 ∂P) =
      (∑ i ∈ Finset.range n, ∫ ω, D i ω ^ 2 ∂P) / ((n : ℝ) + 1) := by
  simp only [normalizedMdsSum, div_pow, Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
  rw [integral_div, integral_mdsSum_sq P F D hD hL2 hzero]

theorem integral_normalizedMdsSum_sq_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ i, (∫ ω, D i ω ^ 2 ∂P) ≤ B) (n : ℕ) :
    (∫ ω, normalizedMdsSum D n ω ^ 2 ∂P) ≤ B := by
  rw [integral_normalizedMdsSum_sq P F D hD hL2 hzero]
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
  calc
    _ ≤ ∑ _i ∈ Finset.range n, B := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (n : ℝ) * B := by simp
    _ ≤ B * ((n : ℝ) + 1) := by nlinarith

lemma mdsSum_congr_ae (P : Measure Ω) {D E : ℕ → Ω → ℝ}
    (hDE : ∀ n, D n =ᵐ[P] E n) (n : ℕ) :
    mdsSum D n =ᵐ[P] mdsSum E n := by
  filter_upwards [ae_all_iff.mpr hDE] with ω hω
  exact Finset.sum_congr rfl (fun i _ => hω i)

theorem bounded_mds_fourth (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ n, ∀ᵐ ω ∂P, |D n ω| ≤ c) (n : ℕ) :
    Integrable (fun ω => mdsSum D n ω ^ 4) P ∧
      (∫ ω, mdsSum D n ω ^ 4 ∂P) ≤ 6 * c ^ 4 * (n : ℝ) ^ 2 := by
  classical
  let E : ℕ → Ω → ℝ := fun i ω => max (-c) (min c ((hD i).mk (D i) ω))
  have hEm (i : ℕ) : Measurable[F (i + 1)] (E i) :=
    measurable_const.max (measurable_const.min (hD i).stronglyMeasurable_mk.measurable)
  have hEglobal (i : ℕ) : Measurable (E i) :=
    ((hEm i).stronglyMeasurable.mono (F.le (i + 1))).measurable
  have hEadapt (i : ℕ) : AEStronglyMeasurable[F (i + 1)] (E i) P :=
    (hEm i).stronglyMeasurable.aestronglyMeasurable
  have hEb (i : ℕ) (ω : Ω) : |E i ω| ≤ c := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hDE (i : ℕ) : D i =ᵐ[P] E i := by
    filter_upwards [(hD i).ae_eq_mk, hbound i] with ω hrep hb
    dsimp only [E]
    rw [← hrep, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  have hEL2 (i : ℕ) : MemLp (E i) 2 P :=
    MemLp.of_bound (hEglobal i).aestronglyMeasurable c
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hEb i ω)
  have hEzero (i : ℕ) : P[E i | F i] =ᵐ[P] 0 :=
    (condExp_congr_ae (hDE i).symm).trans (hzero i)
  have hsecond (i : ℕ) : (∫ ω, mdsSum E i ω ^ 2 ∂P) ≤ (i : ℝ) * c ^ 2 := by
    rw [integral_mdsSum_sq P F E hEadapt hEL2 hEzero]
    calc
      _ ≤ ∑ _j ∈ Finset.range i, c ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hi : Integrable (fun ω => E j ω ^ 2) P :=
          (memLp_two_iff_integrable_sq (hEL2 j).1).mp (hEL2 j)
        calc
          _ ≤ ∫ _ω : Ω, c ^ 2 ∂P := integral_mono hi (integrable_const _) (fun ω => by
            simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hEb j ω) 2)
          _ = c ^ 2 := by simp
      _ = _ := by simp
  have horth (i : ℕ) : (∫ ω, mdsSum E i ω ^ 3 * E i ω ∂P) = 0 := by
    have hi : Integrable (fun ω => mdsSum E i ω ^ 3 * E i ω) P := by
      simpa only [pow_one] using
        FourthRecurrence.integrable_monomial P E hEglobal c hc hEb i 3 1
    exact integral_mul_eq_zero_of_condExp P (F.le i)
      ((mdsSum_aestronglyMeasurable_past P F E hEadapt i).pow 3) hi
      ((hEL2 i).integrable (by norm_num)) (hEzero i)
  have hi4 := FourthRecurrence.integrable_fourth P E hEglobal c hc hEb n
  have hb4 := FourthRecurrence.integral_fourth_le P E hEglobal c hc hEb horth hsecond n
  have hsum : (fun ω => mdsSum D n ω ^ 4) =ᵐ[P]
      (fun ω => mdsSum E n ω ^ 4) := (mdsSum_congr_ae P hDE n).pow_const 4
  refine ⟨hi4.congr hsum.symm, ?_⟩
  rw [integral_congr_ae hsum]
  exact hb4

theorem bounded_normalizedMdsSum_fourth (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ n, ∀ᵐ ω ∂P, |D n ω| ≤ c) (n : ℕ) :
    Integrable (fun ω => normalizedMdsSum D n ω ^ 4) P ∧
      (∫ ω, normalizedMdsSum D n ω ^ 4 ∂P) ≤ 6 * c ^ 4 := by
  obtain ⟨hi, hb⟩ := bounded_mds_fourth P F D hD hzero c hc hbound n
  have hs : Real.sqrt ((n : ℝ) + 1) ^ 4 = ((n : ℝ) + 1) ^ 2 := by
    calc
      _ = (Real.sqrt ((n : ℝ) + 1) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) + 1)]
  simp only [normalizedMdsSum, div_pow, hs]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div]
  apply (div_le_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ 2)).mpr
  have hn : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact hb.trans (mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 6 * c ^ 4))

end

end SummableRhoUI

end UIComponent8

section UIComponent9

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SummableRhoUI

variable {Omega I : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem uniformIntegrable_of_uniform_Lp_approximation
    {p : ENNReal} (hp : 1 <= p) {X : I -> Omega -> Real}
    (hX : forall i, MemLp (X i) p P)
    (happrox : forall eps : Real, 0 < eps ->
      exists G : I -> Omega -> Real, UniformIntegrable G p P /\
        forall i, eLpNorm (X i - G i) p P <= ENNReal.ofReal eps) :
    UniformIntegrable X p P := by
  refine And.intro (fun i => (hX i).aestronglyMeasurable) (And.intro ?_ ?_)
  · intro eps heps
    obtain ⟨G, hG, hdist⟩ := happrox (eps / 2) (half_pos heps)
    obtain ⟨delta, hdelta, hsmall⟩ := hG.unifIntegrable (half_pos heps)
    refine ⟨delta, hdelta, fun i s hs hPs => ?_⟩
    have hid : s.indicator (X i) =
        s.indicator (X i - G i) + s.indicator (G i) := by
      rw [<- indicator_add']
      congr 1
      exact (sub_add_cancel _ _).symm
    rw [hid]
    calc
      eLpNorm (s.indicator (X i - G i) + s.indicator (G i)) p P <=
          eLpNorm (s.indicator (X i - G i)) p P + eLpNorm (s.indicator (G i)) p P :=
        eLpNorm_add_le (((hX i).aestronglyMeasurable.sub
          (hG.aestronglyMeasurable i)).indicator hs)
          ((hG.aestronglyMeasurable i).indicator hs) hp
      _ <= ENNReal.ofReal (eps / 2) + ENNReal.ofReal (eps / 2) :=
        add_le_add ((eLpNorm_indicator_le _).trans (hdist i)) (hsmall i s hs hPs)
      _ = ENNReal.ofReal eps := by
        rw [<- ENNReal.ofReal_add (half_pos heps).le (half_pos heps).le, add_halves]
  · obtain ⟨G, hG, hdist⟩ := happrox 1 zero_lt_one
    obtain ⟨C, hC⟩ := hG.2.2
    refine ⟨C + 1, fun i => ?_⟩
    calc
      eLpNorm (X i) p P = eLpNorm (X i - G i + G i) p P := by rw [sub_add_cancel]
      _ <= eLpNorm (X i - G i) p P + eLpNorm (G i) p P :=
        eLpNorm_add_le ((hX i).aestronglyMeasurable.sub (hG.aestronglyMeasurable i))
          (hG.aestronglyMeasurable i) hp
      _ <= ENNReal.ofReal 1 + C := add_le_add (hdist i) (hC i)
      _ = (C + 1 : NNReal) := by simp [add_comm]

theorem uniformIntegrable_add
    {p : ENNReal} (hp : 1 <= p) {X Y : I -> Omega -> Real}
    (hX : UniformIntegrable X p P) (hY : UniformIntegrable Y p P) :
    UniformIntegrable (fun i x => X i x + Y i x) p P := by
  refine ⟨(fun i => (hX.1 i).add (hY.1 i)),
    hX.unifIntegrable.add hY.unifIntegrable hp hX.1 hY.1, ?_⟩
  obtain ⟨C, hC⟩ := hX.2.2
  obtain ⟨D, hD⟩ := hY.2.2
  refine ⟨C + D, fun i => ?_⟩
  exact (eLpNorm_add_le (hX.1 i) (hY.1 i) hp).trans (by exact_mod_cast add_le_add (hC i) (hD i))

theorem uniformIntegrable_comp
    {p : ENNReal} {X : I -> Omega -> Real} (hX : UniformIntegrable X p P)
    {J : Type*} (r : J -> I) : UniformIntegrable (fun j => X (r j)) p P := by
  refine ⟨fun j => hX.1 (r j), ?_, ?_⟩
  · intro eps heps
    obtain ⟨d, hd, hsmall⟩ := hX.unifIntegrable heps
    exact ⟨d, hd, fun j => hsmall (r j)⟩
  · obtain ⟨C, hC⟩ := hX.2.2
    exact ⟨C, fun j => hC (r j)⟩

theorem uniformIntegrable_of_Lp_null
    {p : ENNReal} (hp : 1 <= p) (hpt : p ≠ ⊤)
    {X : Nat -> Omega -> Real} (hX : forall n, MemLp (X n) p P)
    (hnull : Tendsto (fun n => eLpNorm (X n) p P) atTop (𝓝 0)) :
    UniformIntegrable X p P := by
  refine ⟨fun n => (hX n).1, unifIntegrable_of_tendsto_Lp_zero hp hpt hX hnull, ?_⟩
  have ht : Tendsto (fun n => (eLpNorm (X n) p P).toReal) atTop (𝓝 (0 : Real)) := by
    simpa using (ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hnull
  obtain ⟨C, hC⟩ := ht.bddAbove_range
  refine ⟨Real.toNNReal C, fun n => ?_⟩
  change eLpNorm (X n) p P <= ENNReal.ofReal C
  rw [<- ENNReal.ofReal_toReal (hX n).2.ne]
  exact ENNReal.ofReal_le_ofReal (hC ⟨n, rfl⟩)

theorem uniformIntegrable_add_Lp_null
    {p : ENNReal} (hp : 1 <= p) (hpt : p ≠ ⊤)
    {X R : Nat -> Omega -> Real} (hX : UniformIntegrable X p P)
    (hR : forall n, MemLp (R n) p P)
    (hnull : Tendsto (fun n => eLpNorm (R n) p P) atTop (𝓝 0)) :
    UniformIntegrable (fun n x => X n x + R n x) p P :=
  uniformIntegrable_add hp hX (uniformIntegrable_of_Lp_null hp hpt hR hnull)

theorem eLpNorm_square (f : Omega -> Real) (p : ENNReal) :
    eLpNorm (fun x => f x ^ 2) p P = eLpNorm f (p * 2) P ^ 2 := by
  simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_ofNat,
    ENNReal.rpow_two] using (eLpNorm_norm_rpow (p := p) (μ := P) f (by norm_num : (0 : Real) < 2))

theorem uniformIntegrable_square {X : I -> Omega -> Real}
    (hX : UniformIntegrable X 2 P) :
    UniformIntegrable (fun i x => X i x ^ 2) 1 P := by
  refine ⟨fun i => (hX.1 i).pow 2, ?_, ?_⟩
  · intro eps heps
    obtain ⟨d, hd, hsmall⟩ := hX.unifIntegrable (Real.sqrt_pos.2 heps)
    refine ⟨d, hd, fun i s hs hPs => ?_⟩
    have hid : s.indicator (fun x => X i x ^ 2) = fun x => (s.indicator (X i) x) ^ 2 := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hid, eLpNorm_square, one_mul]
    calc
      eLpNorm (s.indicator (X i)) 2 P ^ 2 <= ENNReal.ofReal (Real.sqrt eps) ^ 2 :=
        pow_le_pow_left' (hsmall i s hs hPs) 2
      _ = ENNReal.ofReal eps := by
        rw [<- ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt heps.le]
  · obtain ⟨C, hC⟩ := hX.2.2
    refine ⟨C ^ 2, fun i => ?_⟩
    rw [eLpNorm_square, one_mul, ENNReal.coe_pow]
    exact pow_le_pow_left' (hC i) 2

theorem uniformIntegrable_bounded_mul
    {p : ENNReal} {X : I -> Omega -> Real} (hX : UniformIntegrable X p P)
    {a : I -> Real} (C : NNReal) (ha : forall i, |a i| <= C) :
    UniformIntegrable (fun i x => a i * X i x) p P := by
  have hnorm : forall i, ‖a i‖ₑ <= (C : ENNReal) := by
    intro i
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_of_le_toReal (by simpa using ha i)
  refine ⟨fun i => (hX.1 i).const_mul (a i), ?_, ?_⟩
  · intro eps heps
    have hCpos : (0 : Real) < C + 1 := by positivity
    obtain ⟨d, hd, hsmall⟩ := hX.unifIntegrable (div_pos heps hCpos)
    refine ⟨d, hd, fun i s hs hPs => ?_⟩
    have hid : s.indicator (fun x => a i * X i x) = a i • s.indicator (X i) := by
      ext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hid, eLpNorm_const_smul]
    calc
      ‖a i‖ₑ * eLpNorm (s.indicator (X i)) p P <=
          (C : ENNReal) * ENNReal.ofReal (eps / (C + 1)) :=
        mul_le_mul' (hnorm i) (hsmall i s hs hPs)
      _ <= ENNReal.ofReal (C + 1) * ENNReal.ofReal (eps / (C + 1)) := by
        gcongr
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (ENNReal.ofReal_le_ofReal (show (C : Real) <= (C : Real) + 1 by linarith))
      _ = ENNReal.ofReal eps := by
        rw [<- ENNReal.ofReal_mul hCpos.le, mul_div_cancel₀ _ hCpos.ne']
  · obtain ⟨D, hD⟩ := hX.2.2
    refine ⟨C * D, fun i => ?_⟩
    change eLpNorm (a i • X i) p P <= _
    rw [eLpNorm_const_smul, ENNReal.coe_mul]
    exact mul_le_mul' (hnorm i) (hD i)

theorem uniformIntegrable_of_succ
    {p : ENNReal} (hp : 1 <= p) (hpt : p ≠ ⊤)
    {X : Nat -> Omega -> Real} (hzero : MemLp (X 0) p P)
    (htail : UniformIntegrable (fun n => X (n + 1)) p P) :
    UniformIntegrable X p P := by
  have hz : UniformIntegrable (fun _ : Unit => X 0) p P :=
    uniformIntegrable_const hp hpt hzero
  obtain ⟨C, hC⟩ := hz.2.2
  obtain ⟨D, hD⟩ := htail.2.2
  refine ⟨?_, ?_, max C D, ?_⟩
  · intro n
    cases n with
    | zero => exact hzero.1
    | succ n => exact htail.1 n
  · intro eps heps
    obtain ⟨d, hd, hsmall⟩ := hz.unifIntegrable heps
    obtain ⟨e, he, hsmall'⟩ := htail.unifIntegrable heps
    refine ⟨min d e, lt_min hd he, fun n s hs hPs => ?_⟩
    cases n with
    | zero => exact hsmall () s hs (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    | succ n => exact hsmall' n s hs (hPs.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _)))
  · intro n
    cases n with
    | zero => exact (hC ()).trans (by exact_mod_cast le_max_left C D)
    | succ n => exact (hD n).trans (by exact_mod_cast le_max_right C D)

end SummableRhoUI

end UIComponent9

section UIComponent10

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SummableRhoUI

variable {Omega I : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem uniformIntegrable_two_of_bounded_four
    [IsProbabilityMeasure P] {X : I -> Omega -> Real}
    (hX : forall i, AEStronglyMeasurable (X i) P)
    (C : NNReal) (hC : forall i, eLpNorm (X i) 4 P <= C) :
    UniformIntegrable X 2 P := by
  refine ⟨hX, ?_, C, fun i =>
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ENNReal) <= 4) (hX i)).trans (hC i)⟩
  intro eps heps
  have hCpos : (0 : Real) < C + 1 := by positivity
  let r : Real := eps / (C + 1)
  have hr : 0 < r := div_pos heps hCpos
  refine ⟨r ^ 4, pow_pos hr 4, fun i s hs hPs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have hroot : (ENNReal.ofReal (r ^ 4)) ^ (1 / 4 : Real) = ENNReal.ofReal r := by
    rw [ENNReal.ofReal_pow hr.le, <- ENNReal.rpow_natCast,
      <- ENNReal.rpow_mul]
    norm_num
  calc
    eLpNorm (X i) 2 (P.restrict s) <=
        eLpNorm (X i) 4 (P.restrict s) * P s ^ (1 / 4 : Real) := by
      convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := P.restrict s) (by norm_num : (2 : ENNReal) <= 4) (hX i).restrict using 1
      norm_num
    _ <= (C : ENNReal) * (ENNReal.ofReal (r ^ 4)) ^ (1 / 4 : Real) :=
      mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i))
        (ENNReal.rpow_le_rpow hPs (by norm_num))
    _ = (C : ENNReal) * ENNReal.ofReal r := by rw [hroot]
    _ <= ENNReal.ofReal ((C : Real) + 1) * ENNReal.ofReal r := by
      gcongr
      simpa only [ENNReal.ofReal_coe_nnreal] using
        (ENNReal.ofReal_le_ofReal (show (C : Real) <= (C : Real) + 1 by linarith))
    _ = ENNReal.ofReal eps := by
      rw [<- ENNReal.ofReal_mul hCpos.le]
      congr 1
      exact mul_div_cancel₀ eps hCpos.ne'

theorem eLpNorm_fourth (f : Omega -> Real) :
    eLpNorm (fun x => f x ^ 4) 1 P = eLpNorm f 4 P ^ 4 := by
  have heq : (fun x => f x ^ 4) = fun x => (f x ^ 2) ^ 2 := by
    ext x
    ring
  rw [heq, eLpNorm_square, one_mul, eLpNorm_square]
  norm_num [<- pow_mul]

theorem uniformIntegrable_two_of_fourth_moment
    [IsProbabilityMeasure P] {X : I -> Omega -> Real}
    (hX : forall i, AEStronglyMeasurable (X i) P)
    (hint : forall i, Integrable (fun x => X i x ^ 4) P)
    (C : NNReal) (hC : forall i, (∫ x, X i x ^ 4 ∂P) <= C) :
    UniformIntegrable X 2 P := by
  have hpow : forall i, eLpNorm (X i) 4 P ^ 4 <= (C : ENNReal) := by
    intro i
    rw [<- eLpNorm_fourth]
    rw [eLpNorm_one_eq_lintegral_enorm]
    have heq : (fun x => ‖X i x ^ 4‖ₑ) = fun x => ENNReal.ofReal (X i x ^ 4) := by
      ext x
      rw [Real.enorm_eq_ofReal (by positivity)]
    rw [heq, <- ofReal_integral_eq_lintegral_ofReal (hint i) (by filter_upwards with x using by positivity)]
    exact ENNReal.ofReal_le_of_le_toReal (by simpa using hC i)
  apply uniformIntegrable_two_of_bounded_four hX (C + 1)
  intro i
  have hbig : (C : ENNReal) <= ((C + 1 : NNReal) : ENNReal) ^ 4 := by
    exact_mod_cast (show C <= (C + 1) ^ 4 by nlinarith [sq_nonneg C, sq_nonneg (C * C)])
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : Real) < 4)).1
  simpa only [<- ENNReal.rpow_natCast] using (hpow i).trans hbig

end SummableRhoUI

end UIComponent10

section UIComponent11

open MeasureTheory
open scoped ENNReal NNReal

namespace SummableRhoUI

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

lemma eLpNorm_two_sq_eq_integral (P : Measure Ω) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    eLpNorm f 2 P ^ 2 = ENNReal.ofReal (∫ ω, f ω ^ 2 ∂P) := by
  have hs : eLpNorm (fun ω => f ω ^ 2) 1 P = eLpNorm f 2 P ^ 2 := by
    simpa only [one_mul] using eLpNorm_square (P := P) f 1
  rw [← hs, eLpNorm_one_eq_lintegral_enorm]
  have heq : (fun ω => ‖f ω ^ 2‖ₑ) = fun ω => ENNReal.ofReal (f ω ^ 2) := by
    funext ω
    exact Real.enorm_eq_ofReal (sq_nonneg _)
  rw [heq]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq hf.1).mp hf)
    (Filter.Eventually.of_forall fun ω => sq_nonneg (f ω))).symm

lemma eLpNorm_two_le_iff_integral_sq_le (P : Measure Ω) {f : Ω → ℝ}
    (hf : MemLp f 2 P) {B : ℝ} (hB : 0 ≤ B) :
    eLpNorm f 2 P ≤ ENNReal.ofReal B ↔ (∫ ω, f ω ^ 2 ∂P) ≤ B ^ 2 := by
  rw [← ENNReal.pow_le_pow_left_iff (by decide : (2 : ℕ) ≠ 0),
    eLpNorm_two_sq_eq_integral P hf, ← ENNReal.ofReal_pow hB,
    ENNReal.ofReal_le_ofReal_iff (sq_nonneg B)]

noncomputable def centeredMdsApproximation (P : Measure Ω)
    (F : Filtration ℕ m0) (W : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  W n - P[W n | F n]

lemma centeredMdsApproximation_adapted (P : Measure Ω) (F : Filtration ℕ m0)
    (W : ℕ → Ω → ℝ)
    (hW : ∀ n, AEStronglyMeasurable[F (n + 1)] (W n) P) (n : ℕ) :
    AEStronglyMeasurable[F (n + 1)] (centeredMdsApproximation P F W n) P :=
  (hW n).sub ((stronglyMeasurable_condExp.mono (F.mono (Nat.le_succ n))).aestronglyMeasurable)

lemma centeredMdsApproximation_memLp (P : Measure Ω) (F : Filtration ℕ m0)
    (W : ℕ → Ω → ℝ) (hW : ∀ n, MemLp (W n) 2 P) (n : ℕ) :
    MemLp (centeredMdsApproximation P F W n) 2 P :=
  (hW n).sub (hW n).condExp

lemma centeredMdsApproximation_condExp (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (W : ℕ → Ω → ℝ)
    (hW : ∀ n, Integrable (W n) P) (n : ℕ) :
    P[centeredMdsApproximation P F W n | F n] =ᵐ[P] 0 := by
  haveI : IsFiniteMeasure (P.trim (F.le n)) := isFiniteMeasure_trim (F.le n)
  have hsub := condExp_sub (hW n)
    (integrable_condExp (μ := P) (m := F n) (f := W n)) (F n)
  have htower := condExp_condExp_of_le (μ := P) (f := W n) le_rfl (F.le n)
  filter_upwards [hsub, htower] with ω hω ht
  simpa only [centeredMdsApproximation, Pi.sub_apply, ht, sub_self, Pi.zero_apply] using hω

lemma centeredMdsApproximation_bound (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (W : ℕ → Ω → ℝ)
    (hW : ∀ n, Integrable (W n) P) (B : ℝ)
    (hB : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ B) (n : ℕ) :
    ∀ᵐ ω ∂P, |centeredMdsApproximation P F W n ω| ≤ 2 * B := by
  have hlo : (fun _ : Ω => -B) ≤ᵐ[P] W n := (hB n).mono fun _ h => (abs_le.mp h).1
  have hhi : W n ≤ᵐ[P] (fun _ : Ω => B) := (hB n).mono fun _ h => (abs_le.mp h).2
  have h₁ := condExp_mono (m := F n) (integrable_const (-B)) (hW n) hlo
  have h₂ := condExp_mono (m := F n) (hW n) (integrable_const B) hhi
  rw [condExp_const (F.le n) (-B)] at h₁
  rw [condExp_const (F.le n) B] at h₂
  filter_upwards [h₁, h₂, hB n] with ω h₁ h₂ hb
  have hce : |(P[W n | F n]) ω| ≤ B := abs_le.mpr ⟨h₁, h₂⟩
  exact (abs_sub (W n ω) ((P[W n | F n]) ω)).trans (by linarith)

lemma centeredMdsApproximation_error (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D W : ℕ → Ω → ℝ)
    (hD : ∀ n, MemLp (D n) 2 P) (hW : ∀ n, MemLp (W n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0) (n : ℕ) :
    eLpNorm (D n - centeredMdsApproximation P F W n) 2 P ≤
      2 * eLpNorm (D n - W n) 2 P := by
  have hsub := condExp_sub ((hD n).integrable (by norm_num))
    ((hW n).integrable (by norm_num)) (F n)
  have heq : D n - centeredMdsApproximation P F W n =ᵐ[P]
      (D n - W n) - P[D n - W n | F n] := by
    filter_upwards [hsub, hzero n] with ω hs hz
    simp only [Pi.sub_apply, Pi.zero_apply] at hs hz
    simp only [centeredMdsApproximation, Pi.sub_apply, hs, hz]
    ring
  rw [eLpNorm_congr_ae heq, two_mul]
  exact (eLpNorm_sub_le ((hD n).sub (hW n)).1
    (((hD n).sub (hW n)).condExp).1 (by norm_num)).trans
      (add_le_add le_rfl eLpNorm_condExp_le)

omit m0 in
lemma normalizedMdsSum_sub (D E : ℕ → Ω → ℝ) (n : ℕ) :
    normalizedMdsSum (fun i => D i - E i) n =
      normalizedMdsSum D n - normalizedMdsSum E n := by
  funext ω
  simp only [normalizedMdsSum, mdsSum, FourthRecurrence.partialSum,
    Pi.sub_apply, Finset.sum_sub_distrib, sub_div]

theorem eLpNorm_normalizedMdsSum_le (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ m0) (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n, eLpNorm (D n) 2 P ≤ ENNReal.ofReal B) (n : ℕ) :
    eLpNorm (normalizedMdsSum D n) 2 P ≤ ENNReal.ofReal B := by
  apply (eLpNorm_two_le_iff_integral_sq_le P (memLp_normalizedMdsSum P D hL2 n) hB).2
  exact integral_normalizedMdsSum_sq_le P F D hD hL2 hzero (B ^ 2)
    (sq_nonneg B) (fun i => (eLpNorm_two_le_iff_integral_sq_le P (hL2 i) hB).1 (hbound i)) n

theorem uniformIntegrable_normalizedMdsSum_of_bounded_approximation
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ m0)
    (D : ℕ → Ω → ℝ)
    (hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P)
    (hL2 : ∀ n, MemLp (D n) 2 P)
    (hzero : ∀ n, P[D n | F n] =ᵐ[P] 0)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (B : ℝ) (_ : 0 ≤ B) (W : ℕ → Ω → ℝ),
      (∀ n, AEStronglyMeasurable[F (n + 1)] (W n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ B) ∧
      ∀ n, eLpNorm (D n - W n) 2 P ≤ ENNReal.ofReal ε) :
    UniformIntegrable (normalizedMdsSum D) 2 P := by
  apply uniformIntegrable_of_uniform_Lp_approximation (by norm_num)
    (memLp_normalizedMdsSum P D hL2)
  intro ε hε
  obtain ⟨B, hB, W, hWa, hWb, hWe⟩ := happrox (ε / 2) (half_pos hε)
  have hW : ∀ n, MemLp (W n) 2 P := fun n =>
    MemLp.of_bound (AEStronglyMeasurable.mono (F.le (n + 1)) (hWa n)) B
      ((hWb n).mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)
  have hWi : ∀ n, Integrable (W n) P := fun n => (hW n).integrable (by norm_num)
  let Z := centeredMdsApproximation P F W
  have hZa := centeredMdsApproximation_adapted P F W hWa
  have hZ2 := centeredMdsApproximation_memLp P F W hW
  have hZzero := centeredMdsApproximation_condExp P F W hWi
  have hZb := centeredMdsApproximation_bound P F W hWi B hWb
  have hUI : UniformIntegrable (normalizedMdsSum Z) 2 P := by
    apply uniformIntegrable_two_of_fourth_moment
      (fun n => (memLp_normalizedMdsSum P Z hZ2 n).1)
      (fun n => (bounded_normalizedMdsSum_fourth P F Z hZa hZzero
        (2 * B) (by positivity) hZb n).1)
      ⟨6 * (2 * B) ^ 4, by positivity⟩
    intro n
    exact (bounded_normalizedMdsSum_fourth P F Z hZa hZzero
      (2 * B) (by positivity) hZb n).2
  refine ⟨normalizedMdsSum Z, hUI, ?_⟩
  have hEa : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n - Z n) P :=
    fun n => (hD n).sub (hZa n)
  have hE2 : ∀ n, MemLp (D n - Z n) 2 P := fun n => (hL2 n).sub (hZ2 n)
  have hEzero : ∀ n, P[D n - Z n | F n] =ᵐ[P] 0 := by
    intro n
    filter_upwards [condExp_sub ((hL2 n).integrable (by norm_num))
      ((hZ2 n).integrable (by norm_num)) (F n), hzero n, hZzero n] with ω hs hd hz
    simpa only [Pi.sub_apply, hd, hz, Pi.zero_apply, sub_self] using hs
  have hEb : ∀ n, eLpNorm (D n - Z n) 2 P ≤ ENNReal.ofReal ε := by
    intro n
    calc
      _ ≤ 2 * eLpNorm (D n - W n) 2 P := centeredMdsApproximation_error P F D W hL2 hW hzero n
      _ ≤ 2 * ENNReal.ofReal (ε / 2) := mul_le_mul' le_rfl (hWe n)
      _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  intro n
  rw [← normalizedMdsSum_sub]
  exact eLpNorm_normalizedMdsSum_le P F (fun i => D i - Z i) hEa hE2 hEzero ε hε.le hEb n

end SummableRhoUI

end UIComponent11

section UIComponent12

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SummableRhoUI

variable {Omega I : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem eLpNorm_coe_L2 (f : Lp Real 2 P) :
    eLpNorm f 2 P = ENNReal.ofReal ‖f‖ := by
  rw [<- Lp.enorm_def, ofReal_norm]

theorem eLpNorm_sub_coe_L2 (f g : Lp Real 2 P) :
    eLpNorm (fun x => f x - g x) 2 P = ENNReal.ofReal ‖f - g‖ := by
  exact (eLpNorm_congr_ae (p := 2) (Lp.coeFn_sub f g)).symm.trans
    (eLpNorm_coe_L2 (f - g))

theorem eLpNorm_div_coe_L2 (f : Lp Real 2 P) {a : Real} (ha : 0 < a) :
    eLpNorm (fun x => f x / a) 2 P = ENNReal.ofReal (‖f‖ / a) := by
  simp only [div_eq_inv_mul]
  change eLpNorm (a⁻¹ • (f : Omega -> Real)) 2 P = _
  rw [eLpNorm_const_smul, eLpNorm_coe_L2, Real.enorm_eq_ofReal (inv_nonneg.2 ha.le),
    <- ENNReal.ofReal_mul (inv_nonneg.2 ha.le)]

theorem eLpNorm_sqrt_normalized_tendsto_zero
    (R : Nat -> Lp Real 2 P) (C : Real) (hC : forall n, ‖R n‖ <= C) :
    Tendsto (fun n : Nat =>
      eLpNorm (fun x => R n x / Real.sqrt ((n : Real) + 1)) 2 P) atTop (𝓝 0) := by
  have htop : Tendsto (fun n : Nat => Real.sqrt ((n : Real) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun n : Nat => ENNReal.ofReal (C / Real.sqrt ((n : Real) + 1)))
      atTop (𝓝 0) := by
    simpa using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_const_nhds.div_atTop htop :
        Tendsto (fun n : Nat => C / Real.sqrt ((n : Real) + 1)) atTop (𝓝 0))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) (fun n => ?_)
  have hn : 0 < Real.sqrt ((n : Real) + 1) := Real.sqrt_pos.2 (by positivity)
  rw [eLpNorm_div_coe_L2 (R n) hn]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hC n) hn.le)

theorem uniformIntegrable_of_uniform_L2_approximation
    (X : I -> Lp Real 2 P)
    (happrox : forall eps : Real, 0 < eps -> exists G : I -> Lp Real 2 P,
      UniformIntegrable (fun i x => G i x) 2 P /\ forall i, ‖X i - G i‖ <= eps) :
    UniformIntegrable (fun i x => X i x) 2 P := by
  apply uniformIntegrable_of_uniform_Lp_approximation (by norm_num) (fun i => Lp.memLp (X i))
  intro eps heps
  obtain ⟨G, hG, hdist⟩ := happrox eps heps
  refine ⟨fun i x => G i x, hG, fun i => ?_⟩
  change eLpNorm (fun x => X i x - G i x) 2 P <= _
  rw [eLpNorm_sub_coe_L2]
  exact ENNReal.ofReal_le_ofReal (hdist i)

end SummableRhoUI

end UIComponent12

section UIComponent13

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem uniformIntegrable_projective_partialSums
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℕ mΩ)
    (x : ℕ → Lp ℝ 2 P) (hx : ∀ n, AEStronglyMeasurable[F n] (x n) P)
    (a : ℕ → ℝ) (ha : Summable a)
    (hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ (B : ℝ) (_ : 0 ≤ B) (w : ℕ → Lp ℝ 2 P),
      (∀ n, AEStronglyMeasurable[F n] (w n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |w n ω| ≤ B) ∧ ∀ n, ‖x n - w n‖ ≤ δ) :
    UniformIntegrable (fun n ω =>
      (∑ i ∈ Finset.range (n + 1), x i ω) / Real.sqrt ((n : ℝ) + 1)) 2 P := by
  have hs := projective_summable P F x a ha hbound
  let D : ℕ → Ω → ℝ := fun n ω => projectiveIncrement P F x n ω
  have hD : ∀ n, AEStronglyMeasurable[F (n + 1)] (D n) P :=
    projectiveIncrement_adapted P F x hx hs
  have hD2 : ∀ n, MemLp (D n) 2 P := fun n => Lp.memLp (projectiveIncrement P F x n)
  have hDzero : ∀ n, P[D n | F n] =ᵐ[P] 0 := projectiveIncrement_condExp_zero P F x hs
  have hDapprox : ∀ ε : ℝ, 0 < ε → ∃ (B : ℝ) (_ : 0 ≤ B) (W : ℕ → Ω → ℝ),
      (∀ n, AEStronglyMeasurable[F (n + 1)] (W n) P) ∧
      (∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ B) ∧
      ∀ n, eLpNorm (D n - W n) 2 P ≤ ENNReal.ofReal ε :=
    projectiveIncrement_bounded_approximation P F x a ha hbound happrox
  have hM := uniformIntegrable_normalizedMdsSum_of_bounded_approximation
    P F D hD hD2 hDzero hDapprox
  let R : ℕ → Lp ℝ 2 P := fun n =>
    x 0 + projectiveTail P F x 0 - projectiveTail P F x n
  have hRbound : ∀ n, ‖R n‖ ≤ ‖x 0‖ + 2 * ∑' k, a k := by
    intro n
    have h₁ := norm_sub_le (x 0 + projectiveTail P F x 0) (projectiveTail P F x n)
    have h₂ := norm_add_le (x 0) (projectiveTail P F x 0)
    have h₃ := projectiveTail_norm_le P F x a ha hbound 0
    have h₄ := projectiveTail_norm_le P F x a ha hbound n
    dsimp only [R]
    linarith
  have hR2 : ∀ n, MemLp (fun ω => R n ω / Real.sqrt ((n : ℝ) + 1)) 2 P := by
    intro n
    simpa only [div_eq_mul_inv] using
      (Lp.memLp (R n)).mul_const (Real.sqrt ((n : ℝ) + 1))⁻¹
  have hRnull := eLpNorm_sqrt_normalized_tendsto_zero R _ hRbound
  have hUI := uniformIntegrable_add_Lp_null (by norm_num : (1 : ENNReal) ≤ 2)
    (by simp) hM hR2 hRnull
  apply hUI.ae_eq
  intro n
  have htelescope : (∑ i ∈ Finset.range (n + 1), x i) =
      (∑ i ∈ Finset.range n, projectiveIncrement P F x i) + R n := by
    dsimp only [R]
    rw [partialSum_projective P F x n]
    abel
  filter_upwards [projective_lp_sum_ae P (Finset.range (n + 1)) x,
    projective_lp_sum_ae P (Finset.range n) (projectiveIncrement P F x),
    Lp.coeFn_add (∑ i ∈ Finset.range n, projectiveIncrement P F x i) (R n)]
    with ω hsum hdsum hadd
  have heval := congrArg (fun f : Lp ℝ 2 P => f ω) htelescope
  dsimp only at heval
  rw [hsum, hadd, Pi.add_apply, hdsum] at heval
  change (∑ i ∈ Finset.range n, projectiveIncrement P F x i ω) /
      Real.sqrt ((n : ℝ) + 1) + R n ω / Real.sqrt ((n : ℝ) + 1) = _
  rw [← add_div, ← heval]

end SummableRhoUI

end UIComponent13

section UIComponent14

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

def processPartialSum {Ω : Type*} (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, Y i ω

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem processPartialSum_measurable (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (n : ℕ) : Measurable (processPartialSum Y n) :=
  Finset.measurable_sum _ (fun i _ => hY i)

theorem processPartialSum_memLp (P : Measure Ω) (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) : MemLp (processPartialSum Y n) 2 P :=
  memLp_finsetSum (Finset.range n) (fun i _ => stationary_memLp P Y hY hstat hL2 i)

theorem processPartialSum_integral_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hstat : IsStrictlyStationary P Y) (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) : ∫ ω, processPartialSum Y n ω ∂P = 0 := by
  have hmean (i : ℕ) : ∫ ω, Y i ω ∂P = 0 := by
    simpa only [id_eq] using
      (stationary_integral_comp P Y hY hstat id measurable_id i).trans hcent
  change (∫ ω, ∑ i ∈ Finset.range n, Y i ω ∂P) = 0
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero (fun i _ => hmean i)
  · intro i _
    exact (stationary_memLp P Y hY hstat hL2 i).integrable (by norm_num)

theorem processPartialSum_variance (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hstat : IsStrictlyStationary P Y) (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (hL2 : MemLp (Y 0) 2 P) (n : ℕ) :
    Var[processPartialSum Y n; P] = ∫ ω, processPartialSum Y n ω ^ 2 ∂P := by
  rw [variance_eq_integral (processPartialSum_measurable Y hY n).aemeasurable,
    processPartialSum_integral_zero P Y hY hstat hcent hL2 n]
  simp only [sub_zero]

theorem partialSum_sq_div_tendsto (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, Measurable (Y n))
    (hstat : IsStrictlyStationary P Y) (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (hL2 : MemLp (Y 0) 2 P)
    (hsum : Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P)) :
    Tendsto (fun n : ℕ => (∫ ω, processPartialSum Y (n + 1) ω ^ 2 ∂P) /
      ((n : ℝ) + 1)) atTop (𝓝 (seqAsymptoticVariance P Y)) := by
  have ht := var_partialSum_div_tendsto_of_summable_cov P Y hY hstat hcent hL2 hsum
  have heq (n : ℕ) : Var[∑ i ∈ Finset.range n, Y i; P] =
      ∫ ω, processPartialSum Y n ω ^ 2 ∂P := by
    have hf : (∑ i ∈ Finset.range n, Y i) = processPartialSum Y n := by
      funext ω
      simp only [Finset.sum_apply, processPartialSum]
    rw [hf]
    exact processPartialSum_variance P Y hY hstat hcent hL2 n
  have hsq : Tendsto (fun n : ℕ => (∫ ω, processPartialSum Y n ω ^ 2 ∂P) / (n : ℝ))
      atTop (𝓝 (seqAsymptoticVariance P Y)) := by
    simpa only [heq] using ht
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    hsq.comp (tendsto_add_atTop_nat 1)

end SummableRhoUI

end UIComponent14

section UIComponent15

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace SummableRhoUI

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}

theorem uniformIntegrable_bounded_mul_of_tendsto
    {p : ENNReal} {X : Nat -> Omega -> Real} (hX : UniformIntegrable X p P)
    {a : Nat -> Real} {b : Real} (ha : Tendsto a atTop (𝓝 b)) :
    UniformIntegrable (fun n x => a n * X n x) p P := by
  obtain ⟨C, hC⟩ := ha.abs.bddAbove_range
  apply uniformIntegrable_bounded_mul hX (Real.toNNReal C)
  intro n
  exact (hC ⟨n, rfl⟩).trans (Real.le_coe_toNNReal C)

theorem uniformIntegrable_variance_normalized
    {S : Nat -> Omega -> Real} (hzero : S 0 = 0)
    (hUI : UniformIntegrable (fun n x => S (n + 1) x / Real.sqrt (n + 1)) 2 P)
    {v : Real} (hv : 0 < v)
    (hvar : Tendsto (fun n : Nat =>
      (∫ x, S (n + 1) x ^ 2 ∂P) / (n + 1 : Real)) atTop (𝓝 v)) :
    UniformIntegrable
      (fun n x => S n x ^ 2 / (∫ y, S n y ^ 2 ∂P)) 1 P := by
  apply uniformIntegrable_of_succ (by norm_num) (by simp)
  · simp [hzero]
  have ha : Tendsto (fun n : Nat => (n + 1 : Real) / (∫ x, S (n + 1) x ^ 2 ∂P))
      atTop (𝓝 v⁻¹) := by
    simpa only [inv_div] using hvar.inv₀ hv.ne'
  have h := uniformIntegrable_bounded_mul_of_tendsto (uniformIntegrable_square hUI) ha
  apply h.ae_eq
  intro n
  filter_upwards with x
  have hn : (0 : Real) < n + 1 := by positivity
  rw [div_pow, Real.sq_sqrt hn.le]
  by_cases hd : (∫ y, S (n + 1) y ^ 2 ∂P) = 0
  · simp [hd]
  · field_simp

end SummableRhoUI

end UIComponent15

section UIComponent16

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace SummableRhoUI

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem uniformIntegrable_normalized_partialSums_of_summable_rho
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hrho : Summable fun n => rhoMixingCoef P Y n) :
    UniformIntegrable (fun n ω =>
      processPartialSum Y (n + 1) ω / Real.sqrt ((n : ℝ) + 1)) 2 P := by
  let F := naturalFiltration Y hY
  let x := stationaryLp P Y hY hstat hL2
  let C : ℝ := ‖hL2.toLp (Y 0)‖
  let a : ℕ → ℝ := fun k => rhoMixingCoef P Y (k + 1) * C
  have ha : Summable a := ((summable_nat_add_iff 1).2 hrho).mul_right C
  have hmean (i : ℕ) : ∫ ω, Y i ω ∂P = 0 := by
    simpa only [id_eq] using
      (stationary_integral_comp P Y hY hstat id measurable_id i).trans hcent
  have hbound : ∀ n k, ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤ a k := by
    intro n k
    have h := conditionalL2_norm_le_rho P Y hY n (k + 1) (Y (n + k + 1))
      (coordinate_measurable_future Y (n + k + 1) (n + (k + 1)) (by omega))
      (stationary_memLp P Y hY hstat hL2 (n + k + 1)) (hmean (n + k + 1))
    change ‖conditionalL2 P (F.le n) (x (n + k + 1))‖ ≤
      rhoMixingCoef P Y (k + 1) * ‖x (n + k + 1)‖ at h
    rw [stationaryLp_norm P Y hY hstat hL2 (n + k + 1)] at h
    exact h
  have hUI := uniformIntegrable_projective_partialSums P F x
    (stationaryLp_adapted P Y hY hstat hL2) a ha hbound
    (stationaryLp_bounded_approximation P Y hY hstat hL2)
  have hae : ∀ᵐ ω ∂P, ∀ i, x i ω = Y i ω :=
    ae_all_iff.mpr (stationaryLp_ae P Y hY hstat hL2)
  apply hUI.ae_eq
  intro n
  filter_upwards [hae] with ω hω
  unfold processPartialSum
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hω i)

end SummableRhoUI

end UIComponent16

section UIComponent17

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hrho : Summable fun n => rhoMixingCoef P Y n)
    (hsum : Summable fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P)
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by
  have hzero : SummableRhoUI.processPartialSum Y 0 = 0 := by
    funext ω
    simp [SummableRhoUI.processPartialSum]
  have hUI := SummableRhoUI.uniformIntegrable_normalized_partialSums_of_summable_rho
    P Y hY hstat hcent hL2 hrho
  have hlim := SummableRhoUI.partialSum_sq_div_tendsto P Y hY hstat hcent hL2 hsum
  simpa only [SummableRhoUI.processPartialSum] using
    SummableRhoUI.uniformIntegrable_variance_normalized hzero hUI hvar hlim

end UIComponent17

