-- Prove2me | solution 1 for MarkovChainCLT.integral_pow_four_scaled_sampleAvg_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:49:39.172824+00:00
-- url     : https://prove2.me/submissions/b434e964-c658-411b-ab9f-bcba879ef869

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Theorems.Thm_MarkovChainCLT_condExp_next_coord
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic.GCongr
import Definitions.Def_MarkovAsymptoticVariance
import Theorems.Thm_MarkovChainCLT_integral_sq_sum_mds_le
import Theorems.Thm_MarkovChainCLT_poissonEquation_of_bounded_of_uniformlyErgodic

open MeasureTheory

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

open MeasureTheory

namespace FourthScale

variable {Ω : Type*} [MeasurableSpace Ω]

theorem add_pow_four_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have hsq : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_nonneg (a - b)]
  have hfour := pow_le_pow_left₀ (sq_nonneg (a + b)) hsq 2
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

theorem normalized_fourth (n : ℕ) (x : ℝ) :
    (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * x)) ^ 4 = x ^ 4 / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hs : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      Real.sqrt (n : ℝ) ^ 4 = (Real.sqrt (n : ℝ) ^ 2) ^ 2 := by ring
      _ = (n : ℝ) ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [mul_pow, mul_pow, hs]
  field_simp

theorem add_fourth_integrable_and_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R)
    (c : ℝ) (hbound : ∀ ω, |R ω| ≤ c)
    (hM4 : Integrable (fun ω => M ω ^ 4) μ) :
    Integrable (fun ω => (M ω + R ω) ^ 4) μ ∧
      (∫ ω, (M ω + R ω) ^ 4 ∂μ) ≤ 8 * ((∫ ω, M ω ^ 4 ∂μ) + c ^ 4) := by
  have hRnorm (ω : Ω) : ‖R ω ^ 4‖ ≤ c ^ 4 := by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound ω) 4
  have hR4 : Integrable (fun ω => R ω ^ 4) μ :=
    Integrable.of_bound (hR.pow_const 4).aestronglyMeasurable (c ^ 4)
      (Filter.Eventually.of_forall hRnorm)
  have hRint : (∫ ω, R ω ^ 4 ∂μ) ≤ c ^ 4 := by
    calc
      (∫ ω, R ω ^ 4 ∂μ) ≤ ∫ _ω : Ω, c ^ 4 ∂μ := by
        apply integral_mono hR4 (integrable_const _)
        intro ω
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hRnorm ω)
      _ = c ^ 4 := by simp
  have hsum4 : Integrable (fun ω => (M ω + R ω) ^ 4) μ := by
    apply ((hM4.add hR4).const_mul 8).mono' ((hM.add hR).pow_const 4).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (M ω + R ω) ^ 4)]
    exact add_pow_four_le (M ω) (R ω)
  refine ⟨hsum4, ?_⟩
  calc
    (∫ ω, (M ω + R ω) ^ 4 ∂μ) ≤ ∫ ω, 8 * (M ω ^ 4 + R ω ^ 4) ∂μ :=
      integral_mono hsum4 ((hM4.add hR4).const_mul 8) (fun ω => add_pow_four_le _ _)
    _ = 8 * ((∫ ω, M ω ^ 4 ∂μ) + ∫ ω, R ω ^ 4 ∂μ) := by
      rw [integral_const_mul, integral_add hM4 hR4]
    _ ≤ 8 * ((∫ ω, M ω ^ 4 ∂μ) + c ^ 4) := by linarith

theorem normalized_integrable_and_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M R : ℕ → Ω → ℝ) (hM : ∀ n, Measurable (M n)) (hR : ∀ n, Measurable (R n))
    (c : ℝ) (hc : 0 ≤ c) (hbound : ∀ n ω, |R n ω| ≤ c)
    (hM4 : ∀ n, Integrable (fun ω => M n ω ^ 4) μ)
    (hmoment : ∀ n, (∫ ω, M n ω ^ 4 ∂μ) ≤ 6 * c ^ 4 * (n : ℝ) ^ 2)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ω => (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (M n ω + R n ω))) ^ 4) μ ∧
      (∫ ω, (Real.sqrt (n : ℝ) * ((n : ℝ)⁻¹ * (M n ω + R n ω))) ^ 4 ∂μ) ≤
        56 * c ^ 4 := by
  obtain ⟨hi, hb⟩ := add_fourth_integrable_and_bound μ (M n) (R n) (hM n) (hR n)
    c (hbound n) (hM4 n)
  simp_rw [normalized_fourth]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div]
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  apply (div_le_iff₀ (sq_pos_of_pos hn')).mpr
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsq : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hc4 : 0 ≤ c ^ 4 := pow_nonneg hc 4
  have hscale := mul_le_mul_of_nonneg_left hsq hc4
  have hm := hmoment n
  nlinarith

end FourthScale

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal NNReal
open MarkovChainCLT

namespace FourthChain

set_option maxHeartbeats 200000

variable {X : Type*} [MeasurableSpace X]

theorem integrable_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded
    (C := C) (ae_of_all _ (fun x => by simpa using hC x))⟩

theorem kernel_bound (P : Kernel X X) [IsMarkovKernel P]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∀ x, |∫ y, g y ∂P x| ≤ C := by
  intro x
  apply le_trans abs_integral_le_integral_abs
  have hi := integrable_bounded (P x) (fun y => |g y|)
    (continuous_abs.measurable.comp hg) C (fun y => by simpa using hC y)
  simpa using integral_mono hi (integrable_const C) hC

theorem cubic_innovation_zero (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) [IsProbabilityMeasure π]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, |g x| ≤ C) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n,
        (g (ω (k + 1)) - ∫ y, g y ∂P (ω k))) ^ 3 *
      (g (ω (n + 1)) - ∫ y, g y ∂P (ω n)) ∂chainMeasure P π = 0 := by
  classical
  let ν := chainMeasure P π
  let Pg : X → ℝ := fun x => ∫ y, g y ∂P x
  let D : ℕ → (ℕ → X) → ℝ := fun k ω => g (ω (k + 1)) - Pg (ω k)
  let M : (ℕ → X) → ℝ := fun ω => ∑ k ∈ Finset.range n, D k ω
  have hmle : MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) n) inferInstance
      ≤ (inferInstance : MeasurableSpace (ℕ → X)) :=
    (measurable_frestrictLe (X := fun _ : ℕ => X) n).comap_le
  haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
  have hPgm : Measurable Pg := hg.stronglyMeasurable.integral_kernel.measurable
  have hPgB : ∀ x, |Pg x| ≤ C := kernel_bound P g hg C hC
  have hDm (k : ℕ) : Measurable (D k) :=
    (hg.comp (measurable_pi_apply (k + 1))).sub (hPgm.comp (measurable_pi_apply k))
  have hDB (k : ℕ) (ω : ℕ → X) : |D k ω| ≤ 2 * C := by
    calc
      |D k ω| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hC (ω (k + 1)), hPgB (ω k)]
  have hMm : Measurable M := (Finset.range n).measurable_sum (fun k _ => hDm k)
  have hMB (ω : ℕ → X) : |M ω| ≤ n * (2 * C) := by
    calc
      |M ω| ≤ ∑ k ∈ Finset.range n, |D k ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, 2 * C := Finset.sum_le_sum (fun k _ => hDB k ω)
      _ = n * (2 * C) := by simp
  have hcoord (i : ℕ) (hi : i ≤ n) : Measurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) n) inferInstance] (fun ω : ℕ → X => ω i) := by
    have h1 : Measurable[MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) n)
        inferInstance] (frestrictLe (π := fun _ : ℕ => X) n) :=
      Measurable.of_comap_le le_rfl
    exact (measurable_pi_apply (⟨i, Finset.mem_Iic.mpr hi⟩ : Finset.Iic n)).comp h1
  have hMpast : Measurable[MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) n) inferInstance] M := by
    apply (Finset.range n).measurable_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact (hg.comp (hcoord (k + 1) (by omega))).sub
      (hPgm.comp (hcoord k (by omega)))
  have hgm : Measurable (fun ω : ℕ → X => g (ω (n + 1))) :=
    hg.comp (measurable_pi_apply (n + 1))
  have hpm : Measurable (fun ω : ℕ → X => Pg (ω n)) := hPgm.comp (measurable_pi_apply n)
  have hgi : Integrable (fun ω : ℕ → X => g (ω (n + 1))) ν :=
    integrable_bounded ν _ hgm C (fun ω => hC _)
  have hprod (v : (ℕ → X) → ℝ) (hv : Measurable v) (hvB : ∀ ω, |v ω| ≤ C) :
      Integrable (fun ω => M ω ^ 3 * v ω) ν := by
    apply integrable_bounded ν _ ((hMm.pow_const 3).mul hv) ((n * (2 * C)) ^ 3 * C)
    intro ω
    rw [abs_mul, abs_pow]
    gcongr
    · exact hMB ω
    · exact hvB ω
  have hi1 := hprod _ hgm (fun ω => hC (ω (n + 1)))
  have hi2 := hprod _ hpm (fun ω => hPgB (ω n))
  have hpull : ν[fun ω => M ω ^ 3 * g (ω (n + 1)) | MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) n) inferInstance] =ᵐ[ν]
      (fun ω => M ω ^ 3) * ν[fun ω => g (ω (n + 1)) | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) n) inferInstance] :=
    condExp_mul_of_stronglyMeasurable_left (hMpast.pow_const 3).stronglyMeasurable hi1 hgi
  have hcond : ν[fun ω : ℕ → X => g (ω (n + 1)) | MeasurableSpace.comap
      (frestrictLe (π := fun _ : ℕ => X) n) inferInstance] =ᵐ[ν]
      (fun ω => Pg (ω n)) := (condExp_next_coord P π g hg C hC n).symm
  have hpull_int := integral_congr_ae (μ := ν) hpull
  simp only [Pi.mul_apply] at hpull_int
  have hmul : (∫ ω, M ω ^ 3 * g (ω (n + 1)) ∂ν) =
      ∫ ω, M ω ^ 3 * Pg (ω n) ∂ν := by
    calc
      _ = ∫ ω, (ν[fun ω => M ω ^ 3 * g (ω (n + 1)) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) n) inferInstance]) ω ∂ν :=
        (integral_condExp hmle).symm
      _ = ∫ ω, M ω ^ 3 * (ν[fun ω => g (ω (n + 1)) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) n) inferInstance]) ω ∂ν :=
        hpull_int
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hcond] with ω hω
        rw [hω]
  change (∫ ω, M ω ^ 3 * (g (ω (n + 1)) - Pg (ω n)) ∂ν) = 0
  simp_rw [mul_sub]
  rw [integral_sub hi1 hi2, hmul, sub_self]

end FourthChain

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : MarkovChainCLT.UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      Integrable (fun ω : ℕ → X =>
        (Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π)) ^ 4)
        (MarkovChainCLT.chainMeasure P π)
      ∧ ∫ ω, (Real.sqrt n * (MarkovChainCLT.sampleAvg f n ω - ∫ x, f x ∂π)) ^ 4
          ∂(MarkovChainCLT.chainMeasure P π) ≤ C := by
  classical
  obtain ⟨g, hg, ⟨K₀, hK₀⟩, hpois⟩ :=
    poissonEquation_of_bounded_of_uniformlyErgodic P π huni f hf B hB
  let K : ℝ := max K₀ 0
  have hK0 : 0 ≤ K := le_max_right _ _
  have hK : ∀ x, |g x| ≤ K := fun x => (hK₀ x).trans (le_max_left _ _)
  let Pg : X → ℝ := fun x => ∫ y, g y ∂P x
  have hPgm : Measurable Pg := hg.stronglyMeasurable.integral_kernel.measurable
  have hPgB : ∀ x, |Pg x| ≤ K := FourthChain.kernel_bound P g hg K hK
  let D : ℕ → (ℕ → X) → ℝ := fun k ω => g (ω (k + 1)) - Pg (ω k)
  let M : ℕ → (ℕ → X) → ℝ := FourthRecurrence.partialSum D
  let R : ℕ → (ℕ → X) → ℝ := fun n ω => Pg (ω 0) - Pg (ω n)
  let c : ℝ := 2 * K
  have hc : 0 ≤ c := mul_nonneg (by norm_num) hK0
  have hDm : ∀ k, Measurable (D k) := fun k =>
    (hg.comp (measurable_pi_apply (k + 1))).sub (hPgm.comp (measurable_pi_apply k))
  have hDB : ∀ k ω, |D k ω| ≤ c := by
    intro k ω
    calc
      |D k ω| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
      _ ≤ c := by dsimp [c]; linarith [hK (ω (k + 1)), hPgB (ω k)]
  have horth : ∀ n, ∫ ω, M n ω ^ 3 * D n ω ∂chainMeasure P π = 0 := by
    intro n
    exact FourthChain.cubic_innovation_zero P π g hg K hK0 hK n
  have hsecond : ∀ n, ∫ ω, M n ω ^ 2 ∂chainMeasure P π ≤ n * c ^ 2 := by
    intro n
    exact integral_sq_sum_mds_le P π g hg K hK n
  have hM4 : ∀ n, Integrable (fun ω => M n ω ^ 4) (chainMeasure P π) :=
    FourthRecurrence.integrable_fourth (chainMeasure P π) D hDm c hc hDB
  have hfour : ∀ n, (∫ ω, M n ω ^ 4 ∂chainMeasure P π) ≤ 6 * c ^ 4 * (n : ℝ) ^ 2 :=
    FourthRecurrence.integral_fourth_le (chainMeasure P π) D hDm c hc hDB horth hsecond
  have hMm : ∀ n, Measurable (M n) := FourthRecurrence.measurable_partialSum D hDm
  have hRm : ∀ n, Measurable (R n) := fun n =>
    (hPgm.comp (measurable_pi_apply 0)).sub (hPgm.comp (measurable_pi_apply n))
  have hRB : ∀ n ω, |R n ω| ≤ c := by
    intro n ω
    calc
      |R n ω| ≤ |Pg (ω 0)| + |Pg (ω n)| := abs_sub _ _
      _ ≤ c := by dsimp [c]; linarith [hPgB (ω 0), hPgB (ω n)]
  have htel : ∀ n (ω : ℕ → X),
      (∑ k ∈ Finset.range n, (f (ω (k + 1)) - ∫ x, f x ∂π)) = M n ω + R n ω := by
    intro n ω
    induction n with
    | zero => simp [M, R, FourthRecurrence.partialSum]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      change _ = FourthRecurrence.partialSum D (n + 1) ω + R (n + 1) ω
      rw [FourthRecurrence.partialSum_succ, ih]
      have hp := hpois (ω (n + 1))
      change g (ω (n + 1)) - Pg (ω (n + 1)) = f (ω (n + 1)) - ∫ x, f x ∂π at hp
      dsimp [R, D]
      change M n ω + (Pg (ω 0) - Pg (ω n)) + (f (ω (n + 1)) - ∫ x, f x ∂π) =
        M n ω + (g (ω (n + 1)) - Pg (ω n)) + (Pg (ω 0) - Pg (ω (n + 1)))
      linarith
  refine ⟨56 * c ^ 4, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, zero_pow (by omega : 4 ≠ 0)]
    exact ⟨integrable_zero _ _ _, by simpa using (show (0 : ℝ) ≤ 56 * c ^ 4 by positivity)⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have heq (ω : ℕ → X) :
      Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π) =
        Real.sqrt n * ((n : ℝ)⁻¹ * (M n ω + R n ω)) := by
    rw [← htel n ω]
    congr 1
    dsimp [sampleAvg]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  simp_rw [heq]
  exact FourthScale.normalized_integrable_and_bound (chainMeasure P π) M R hMm hRm
    c hc hRB hM4 hfour n hnpos

#print axioms solution
