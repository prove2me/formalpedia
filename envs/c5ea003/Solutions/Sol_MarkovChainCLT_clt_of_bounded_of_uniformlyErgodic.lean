-- Prove2me | solution 1 for MarkovChainCLT.clt_of_bounded_of_uniformlyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:56:23.974811+00:00
-- url     : https://prove2.me/submissions/5088cb85-e206-4906-8425-754a50895392

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_poissonEquation_of_bounded_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_condExp_next_coord
import Theorems.Thm_MarkovChainCLT_integral_sq_quadVar_sub_le
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_stationary_clt_of_uniformlyErgodic
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MeasureTheory_tendstoInMeasure_inv_sqrt_mul_of_dominated
import Theorems.Thm_Martingale_clt_of_bounded_mds_array
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (huni : UniformlyErgodic P π)
    (f : X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    SatisfiesCLT P π f := by
  classical
  obtain ⟨g, hgm, ⟨C, hgC⟩, hpois⟩ :=
    poissonEquation_of_bounded_of_uniformlyErgodic P π huni f hf B hB
  have hne : Nonempty X := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 : π Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hcon, measure_empty] at h1
    exact zero_ne_one h1
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hgC hne.some)
  set ν : Measure (ℕ → X) := chainMeasure P π with hν
  set c₀ : ℝ := ∫ x, f x ∂π with hc₀
  set Pg : X → ℝ := fun x => ∫ y, g y ∂(P x) with hPg
  have hPgm : Measurable Pg := (hgm.stronglyMeasurable.integral_kernel (κ := P)).measurable
  have hPgC : ∀ x, |Pg x| ≤ C := by
    intro x
    rw [hPg]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun y => |g y|) (P x) :=
      ⟨(continuous_abs.measurable.comp hgm).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun z => by simpa using hgC z))⟩
    have h2 := integral_mono h1 (integrable_const C) (fun z => hgC z)
    simpa using h2
  set D : ℕ → (ℕ → X) → ℝ := fun k ω => g (ω (k + 1)) - Pg (ω k) with hD
  have hDm : ∀ k, Measurable (D k) :=
    fun k => (hgm.comp (measurable_pi_apply (k + 1))).sub (hPgm.comp (measurable_pi_apply k))
  have hDB : ∀ k ω, |D k ω| ≤ 2 * C := by
    intro k ω
    calc |D k ω| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hgC (ω (k + 1)), hPgC (ω k)]
  -- integrals against `π` transfer through the kernel by invariance
  have hinvint : ∀ (h : X → ℝ), Measurable h → ∀ M : ℝ, (∀ x, |h x| ≤ M) →
      ∫ x, (∫ y, h y ∂(P x)) ∂π = ∫ x, h x ∂π := by
    intro h hh M hM
    have hcomp : P ∘ₘ π = (P ∘ₖ Kernel.const Unit π) () := Measure.comp_eq_comp_const_apply
    have hint : Integrable h ((P ∘ₖ Kernel.const Unit π) ()) := by
      rw [← hcomp, hinv]
      exact ⟨hh.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := M) (ae_of_all _ (fun y => by simpa using hM y))⟩
    have h1 : ∫ y, h y ∂(P ∘ₘ π) = ∫ x, (∫ y, h y ∂(P x)) ∂π := by
      rw [hcomp, Kernel.integral_comp hint]
      simp
    rw [← h1, hinv]
  -- the asymptotic variance is nonnegative
  have hjensen : ∀ x : X, (Pg x) ^ 2 ≤ ∫ y, (g y) ^ 2 ∂(P x) := by
    intro x
    have hgi : Integrable g (P x) :=
      ⟨hgm.aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun z => by simpa using hgC z))⟩
    have hg2i : Integrable (fun y => (g y) ^ 2) (P x) :=
      ⟨(hgm.pow_const 2).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C ^ 2) (ae_of_all _ (fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          nlinarith [hgC z, abs_nonneg (g z), sq_abs (g z)]))⟩
    set m : ℝ := Pg x with hm
    have hexp : ∫ y, (g y - m) ^ 2 ∂(P x)
        = (∫ y, (g y) ^ 2 ∂(P x)) - 2 * m * (∫ y, g y ∂(P x)) + m ^ 2 := by
      have hev : ∀ y, (g y - m) ^ 2 = (g y) ^ 2 - 2 * m * g y + m ^ 2 := by
        intro y; ring
      rw [integral_congr_ae (ae_of_all _ hev)]
      have i2 : Integrable (fun y => 2 * m * g y) (P x) := hgi.const_mul (2 * m)
      have i1 : Integrable (fun y => (g y) ^ 2 - 2 * m * g y) (P x) := hg2i.sub i2
      rw [integral_add i1 (integrable_const (m ^ 2)), integral_sub hg2i i2,
        integral_const_mul, integral_const]
      simp [Measure.real]
    have hnn : 0 ≤ ∫ y, (g y - m) ^ 2 ∂(P x) := integral_nonneg (fun y => sq_nonneg _)
    rw [hexp] at hnn
    have : ∫ y, g y ∂(P x) = m := by rw [hm, hPg]
    rw [this] at hnn
    nlinarith [hnn]
  set σ2 : ℝ := (∫ x, (g x) ^ 2 ∂π) - ∫ x, (Pg x) ^ 2 ∂π with hσ2def
  have hg2m : Measurable (fun x => (g x) ^ 2) := hgm.pow_const 2
  have hg2C : ∀ x, |(g x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hgC x, abs_nonneg (g x), sq_abs (g x)]
  have hPg2m : Measurable (fun x => (Pg x) ^ 2) := hPgm.pow_const 2
  have hPg2C : ∀ x, |(Pg x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hPgC x, abs_nonneg (Pg x), sq_abs (Pg x)]
  have hσ2nn : 0 ≤ σ2 := by
    have hker : Measurable (fun x => ∫ y, (g y) ^ 2 ∂(P x)) :=
      (hg2m.stronglyMeasurable.integral_kernel (κ := P)).measurable
    have hkerC : ∀ x, |∫ y, (g y) ^ 2 ∂(P x)| ≤ C ^ 2 := by
      intro x
      refine le_trans abs_integral_le_integral_abs ?_
      have h1 : Integrable (fun y => |(g y) ^ 2|) (P x) :=
        ⟨(continuous_abs.measurable.comp hg2m).aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := C ^ 2)
            (ae_of_all _ (fun z => by simpa using hg2C z))⟩
      have := integral_mono h1 (integrable_const (C ^ 2)) (fun z => hg2C z)
      simpa using this
    have hmono : ∫ x, (Pg x) ^ 2 ∂π ≤ ∫ x, (∫ y, (g y) ^ 2 ∂(P x)) ∂π := by
      refine integral_mono ?_ ?_ hjensen
      · exact ⟨hPg2m.aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := C ^ 2)
            (ae_of_all _ (fun z => by simpa using hPg2C z))⟩
      · exact ⟨hker.aestronglyMeasurable,
          HasFiniteIntegral.of_bounded (C := C ^ 2)
            (ae_of_all _ (fun z => by simpa using hkerC z))⟩
    have heq := hinvint (fun x => (g x) ^ 2) hg2m (C ^ 2) hg2C
    rw [hσ2def]
    linarith [hmono, heq]
  set σ : ℝ := Real.sqrt σ2 with hσdef
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ2nn
  -- the filtration generated by the coordinates up to `k+1`
  have hfle : ∀ k : ℕ,
      MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k) inferInstance
        ≤ (inferInstance : MeasurableSpace (ℕ → X)) :=
    fun k => (measurable_frestrictLe k).comap_le
  have hfmono : Monotone (fun k : ℕ =>
      MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance) := by
    intro i j hij
    have hij' : i + 1 ≤ j + 1 := by omega
    have hcomp : (frestrictLe₂ (π := fun _ : ℕ => X) hij')
          ∘ (frestrictLe (π := fun _ : ℕ => X) (j + 1))
        = frestrictLe (π := fun _ : ℕ => X) (i + 1) :=
      frestrictLe₂_comp_frestrictLe hij'
    show MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (i + 1)) inferInstance
      ≤ MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance
    have h1 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) (j + 1)) := Measurable.of_comap_le le_rfl
    have h2 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (j + 1)) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) (i + 1)) := by
      rw [← hcomp]
      exact (measurable_frestrictLe₂ hij').comp h1
    exact h2.comap_le
  let F : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → X)) :=
    ⟨fun k => MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance,
      hfmono, fun k => hfle (k + 1)⟩
  have hFeq : ∀ k : ℕ, (F k : MeasurableSpace (ℕ → X))
      = MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance :=
    fun k => rfl
  have hcoordF : ∀ (k i : ℕ), i ≤ k + 1 → Measurable[F k] (fun ω : ℕ → X => ω i) := by
    intro k i hi
    have h1 : Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) := Measurable.of_comap_le le_rfl
    have h2 := (measurable_pi_apply (⟨i, Finset.mem_Iic.2 hi⟩ : Finset.Iic (k + 1))).comp h1
    exact h2
  -- the martingale difference array
  set Darr : ℕ → ℕ → (ℕ → X) → ℝ := fun n k ω => (Real.sqrt n)⁻¹ * D k ω with hDarr
  have hDarrm : ∀ n k, Measurable (Darr n k) := fun n k => (hDm k).const_mul _
  have hDarrad : ∀ n k, Measurable[F k] (Darr n k) := by
    intro n k
    exact (((hgm.comp (hcoordF k (k + 1) le_rfl)).sub
      (hPgm.comp (hcoordF k k (by omega))))).const_mul _
  have hDarrint : ∀ n k, Integrable (Darr n k) ν := by
    intro n k
    refine ⟨(hDarrm n k).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := (Real.sqrt n)⁻¹ * (2 * C))
        (ae_of_all _ (fun ω => ?_))⟩
    rw [Real.norm_eq_abs, hDarr, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt n)⁻¹)]
    exact mul_le_mul_of_nonneg_left (hDB k ω) (by positivity)
  -- the martingale property
  have hDcond : ∀ k : ℕ, ν[D (k + 1) | F k] =ᵐ[ν] 0 := by
    intro k
    have hmle : MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance
        ≤ (inferInstance : MeasurableSpace (ℕ → X)) := hfle (k + 1)
    haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
    have hint1 : Integrable (fun ω : ℕ → X => g (ω (k + 1 + 1))) ν :=
      ⟨(hgm.comp (measurable_pi_apply (k + 1 + 1))).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun ω => by simpa using hgC _))⟩
    have hint2 : Integrable (fun ω : ℕ → X => Pg (ω (k + 1))) ν :=
      ⟨(hPgm.comp (measurable_pi_apply (k + 1))).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun ω => by simpa using hPgC _))⟩
    have h1 := (condExp_next_coord P π g hgm C hgC (k + 1)).symm
    have hsmPg : StronglyMeasurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]
        (fun ω : ℕ → X => Pg (ω (k + 1))) := by
      have hx := hPgm.comp (hcoordF k (k + 1) le_rfl)
      exact hx.stronglyMeasurable
    have h2 : ν[fun ω : ℕ → X => Pg (ω (k + 1)) | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]
        =ᵐ[ν] fun ω : ℕ → X => Pg (ω (k + 1)) := by
      rw [condExp_of_stronglyMeasurable hmle hsmPg hint2]
    have h3 : ν[fun ω : ℕ → X => g (ω (k + 1 + 1)) - Pg (ω (k + 1)) | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]
        =ᵐ[ν] ν[fun ω : ℕ → X => g (ω (k + 1 + 1)) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]
          - ν[fun ω : ℕ → X => Pg (ω (k + 1)) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance] :=
      condExp_sub hint1 hint2 _
    filter_upwards [h1, h2, h3] with ω e1 e2 e3
    have e3' : (ν[fun ω : ℕ → X => g (ω (k + 1 + 1)) - Pg (ω (k + 1)) | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]) ω
        = (ν[fun ω : ℕ → X => g (ω (k + 1 + 1)) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]) ω
          - (ν[fun ω : ℕ → X => Pg (ω (k + 1)) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance]) ω := by
      rw [e3]
      rfl
    show (ν[D (k + 1) | F k]) ω = 0
    have hFk : (F k : MeasurableSpace (ℕ → X))
        = MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) (k + 1)) inferInstance := rfl
    rw [hFk, show D (k + 1) = fun ω : ℕ → X => g (ω (k + 1 + 1)) - Pg (ω (k + 1)) from rfl,
      e3', e1, e2]
    simp [hPg]
  have hmds : ∀ n k, ν[Darr n (k + 1) | F k] =ᵐ[ν] 0 := by
    intro n k
    have hsm : ν[(Real.sqrt n)⁻¹ • D (k + 1) | F k]
        =ᵐ[ν] (Real.sqrt n)⁻¹ • ν[D (k + 1) | F k] :=
      condExp_smul (Real.sqrt n)⁻¹ (D (k + 1)) (F k)
    filter_upwards [hsm, hDcond k] with ω a b
    show (ν[Darr n (k + 1) | F k]) ω = 0
    have h0 : (ν[Darr n (k + 1) | F k]) ω
        = (ν[(Real.sqrt n)⁻¹ • D (k + 1) | F k]) ω := rfl
    rw [h0, a]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at b ⊢
    rw [b, mul_zero]
  -- centering
  have hcoordlaw : ∀ i : ℕ, ν.map (fun ω : ℕ → X => ω i) = π := by
    intro i
    exact map_coord_chainMeasure P π hinv i
  have hintcoord : ∀ (h : X → ℝ), Measurable h → ∀ M : ℝ, (∀ x, |h x| ≤ M) → ∀ i : ℕ,
      ∫ ω, h (ω i) ∂ν = ∫ x, h x ∂π := by
    intro h hh M hM i
    have := integral_map (μ := ν) (φ := fun ω : ℕ → X => ω i) (f := h)
      (measurable_pi_apply i).aemeasurable hh.stronglyMeasurable.aestronglyMeasurable
    rw [hcoordlaw i] at this
    exact this.symm
  have hcent : ∀ n : ℕ, ∫ ω, Darr n 0 ω ∂ν = 0 := by
    intro n
    have hi1 : Integrable (fun ω : ℕ → X => g (ω (0 + 1))) ν :=
      ⟨(hgm.comp (measurable_pi_apply (0 + 1))).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun ω => by simpa using hgC _))⟩
    have hi2 : Integrable (fun ω : ℕ → X => Pg (ω 0)) ν :=
      ⟨(hPgm.comp (measurable_pi_apply 0)).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun ω => by simpa using hPgC _))⟩
    have h1 : ∫ ω, D 0 ω ∂ν = 0 := by
      have hsub : ∫ ω, D 0 ω ∂ν
          = (∫ ω, g (ω (0 + 1)) ∂ν) - ∫ ω, Pg (ω 0) ∂ν := integral_sub hi1 hi2
      rw [hsub, hintcoord g hgm C hgC (0 + 1), hintcoord Pg hPgm C hPgC 0,
        hinvint g hgm C hgC]
      ring
    have : ∫ ω, Darr n 0 ω ∂ν = (Real.sqrt n)⁻¹ * ∫ ω, D 0 ω ∂ν := by
      rw [hDarr]
      exact integral_const_mul _ _
    rw [this, h1, mul_zero]
  -- uniform bounds
  set Cn : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ * (2 * C) with hCn
  have hCbdd : ∀ n k ω, |Darr n k ω| ≤ Cn n := by
    intro n k ω
    rw [hDarr, hCn, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt n)⁻¹)]
    exact mul_le_mul_of_nonneg_left (hDB k ω) (by positivity)
  have hCn0 : Tendsto Cn atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      exact h2.inv_tendsto_atTop
    simpa [hCn] using h1.mul_const (2 * C)
  have hinvsq : ∀ n : ℕ, 1 ≤ n → ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
  have hsumsq : ∀ (n : ℕ) (ω : ℕ → X), ∑ k ∈ Finset.range n, (Darr n k ω) ^ 2
      = ((Real.sqrt n)⁻¹) ^ 2 * ∑ k ∈ Finset.range n, (D k ω) ^ 2 := by
    intro n ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hDarr]
    ring
  have hM : ∀ (n : ℕ) (ω : ℕ → X), ∑ k ∈ Finset.range n, (Darr n k ω) ^ 2 ≤ (2 * C) ^ 2 := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      positivity
    · rw [hsumsq n ω, hinvsq n hn]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hbd : ∑ k ∈ Finset.range n, (D k ω) ^ 2 ≤ n * (2 * C) ^ 2 := by
        calc ∑ k ∈ Finset.range n, (D k ω) ^ 2 ≤ ∑ _k ∈ Finset.range n, (2 * C) ^ 2 := by
              refine Finset.sum_le_sum (fun k _ => ?_)
              nlinarith [hDB k ω, abs_nonneg (D k ω), sq_abs (D k ω)]
          _ = n * (2 * C) ^ 2 := by simp [Finset.sum_const, Finset.card_range]
      have hinvpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      have := mul_le_mul_of_nonneg_left hbd hinvpos.le
      have he : (n : ℝ)⁻¹ * ((n : ℝ) * (2 * C) ^ 2) = (2 * C) ^ 2 := by
        field_simp
      linarith [this, he]
  -- convergence of the quadratic variation in L¹
  have hvar : Tendsto (fun n : ℕ => ∫ ω, |(∑ k ∈ Finset.range n, (Darr n k ω) ^ 2) - σ ^ 2| ∂ν)
      atTop (𝓝 0) := by
    obtain ⟨K, hK0, hK⟩ := integral_sq_quadVar_sub_le P π huni π g hgm C hgC
    refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
    obtain ⟨N0, hN0⟩ := exists_nat_gt (K / ε ^ 2)
    refine ⟨max 1 N0, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hnN : N0 ≤ n := le_trans (le_max_right _ _) hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    have hEq : ∀ ω : ℕ → X, (∑ k ∈ Finset.range n, (Darr n k ω) ^ 2) - σ ^ 2
        = ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2 := by
      intro ω
      rw [hsumsq n ω, hinvsq n hn1, hσsq]
    have hYm : Measurable (fun ω : ℕ → X =>
        ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2) :=
      ((Finset.measurable_sum _ (fun k _ => (hDm k).pow_const 2)).const_mul _).sub_const _
    have hYbd : ∀ ω : ℕ → X,
        |((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2| ≤ (2 * C) ^ 2 + σ2 := by
      intro ω
      have h1 : (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2 ≤ (2 * C) ^ 2 := by
        have := hM n ω
        rw [hsumsq n ω, hinvsq n hn1] at this
        exact this
      have h2 : 0 ≤ (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2 := by
        have : (0 : ℝ) ≤ ∑ k ∈ Finset.range n, (D k ω) ^ 2 :=
          Finset.sum_nonneg (fun k _ => sq_nonneg _)
        positivity
      rw [abs_le]
      constructor <;> linarith [hσ2nn]
    have hint1 : Integrable (fun ω : ℕ → X =>
        |((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2|) ν :=
      ⟨(continuous_abs.measurable.comp hYm).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := (2 * C) ^ 2 + σ2)
          (ae_of_all _ (fun ω => by simpa using hYbd ω))⟩
    have hint2 : Integrable (fun ω : ℕ → X =>
        (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2) ^ 2) ν :=
      ⟨(hYm.pow_const 2).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := ((2 * C) ^ 2 + σ2) ^ 2)
          (ae_of_all _ (fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            nlinarith [hYbd ω, abs_nonneg (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              (D k ω) ^ 2) - σ2), sq_abs (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
              (D k ω) ^ 2) - σ2), hσ2nn, sq_nonneg (2 * C)]))⟩
    have hpt : ∀ ω : ℕ → X,
        |((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2|
          ≤ ε / 2 + (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2) ^ 2 * (2 * ε)⁻¹ := by
      intro ω
      set y : ℝ := ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2 with hy
      have hεpos : (0 : ℝ) < ε := hε
      have hkey : |y| * (2 * ε) ≤ (ε / 2) * (2 * ε) + y ^ 2 := by
        nlinarith [sq_nonneg (|y| - ε), abs_nonneg y, sq_abs y]
      have h2 : (0 : ℝ) < 2 * ε := by linarith
      rw [← le_div_iff₀ h2] at hkey
      calc |y| ≤ (ε / 2 * (2 * ε) + y ^ 2) / (2 * ε) := hkey
        _ = ε / 2 + y ^ 2 * (2 * ε)⁻¹ := by field_simp
    have hic : Integrable (fun _ω : ℕ → X => ε / 2) ν := integrable_const _
    have hid : Integrable (fun ω : ℕ → X =>
        (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2) ^ 2 / (2 * ε)) ν :=
      hint2.div_const (2 * ε)
    have hmono := integral_mono hint1 (hic.add hid) (fun ω => by
      have := hpt ω
      simpa [div_eq_mul_inv] using this)
    simp only [Pi.add_apply] at hmono
    rw [integral_add hic hid, integral_const, integral_div] at hmono
    have hKn : ∫ ω, (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2) ^ 2 ∂ν ≤ K / n :=
      hK n hn1
    have hlast : K / n / (2 * ε) < ε / 2 := by
      have hNn : K / ε ^ 2 < n := lt_of_lt_of_le hN0 (by exact_mod_cast hnN)
      have h2 : (0 : ℝ) < 2 * ε := by linarith
      rw [div_div, div_lt_iff₀ (by positivity)]
      have : K < n * ε ^ 2 := by
        rw [div_lt_iff₀ (by positivity)] at hNn
        linarith
      nlinarith [this, hε]
    have hfinal : ∫ ω, |((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2| ∂ν < ε := by
      have h2 : (0 : ℝ) < 2 * ε := by linarith
      have hdiv : (∫ ω, (((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2) ^ 2 ∂ν)
          / (2 * ε) ≤ K / n / (2 * ε) := by
        exact div_le_div_of_nonneg_right hKn h2.le
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hmono
      linarith
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))]
    calc ∫ ω, |(∑ k ∈ Finset.range n, (Darr n k ω) ^ 2) - σ ^ 2| ∂ν
        = ∫ ω, |((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (D k ω) ^ 2) - σ2| ∂ν := by
          refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
          simp only
          rw [hEq ω]
      _ < ε := hfinal
  -- the martingale central limit theorem
  have hmart := Martingale.clt_of_bounded_mds_array ν F Darr hDarrm hDarrad hDarrint hmds
    hcent Cn hCbdd hCn0 ((2 * C) ^ 2) hM σ hvar
  -- the telescoping remainder
  set W : ℕ → (ℕ → X) → ℝ := fun n ω => Pg (ω 0) - Pg (ω n) with hW
  have hWdom : ∀ n ω, |W n ω| ≤ 2 * C := by
    intro n ω
    calc |W n ω| ≤ |Pg (ω 0)| + |Pg (ω n)| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hPgC (ω 0), hPgC (ω n)]
  have hident : ∀ (n : ℕ) (ω : ℕ → X),
      Real.sqrt n * (sampleAvg f n ω - c₀) - (∑ k ∈ Finset.range n, Darr n k ω)
        = (Real.sqrt n)⁻¹ * W n ω := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [sampleAvg, hW]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
      have e1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
        rw [← div_eq_mul_inv, Real.sqrt_div_self', one_div]
      have e2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
        rw [inv_mul_eq_div, Real.div_sqrt]
      have hstep : ∀ k, f (ω (k + 1)) - c₀ = D k ω + (Pg (ω k) - Pg (ω (k + 1))) := by
        intro k
        have := hpois (ω (k + 1))
        simp only [hD, hPg] at *
        linarith
      have hsum : (∑ k ∈ Finset.range n, f (ω (k + 1))) - (n : ℝ) * c₀
          = (∑ k ∈ Finset.range n, D k ω) + W n ω := by
        have h1 : (∑ k ∈ Finset.range n, f (ω (k + 1))) - (n : ℝ) * c₀
            = ∑ k ∈ Finset.range n, (f (ω (k + 1)) - c₀) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
          simp [mul_comm]
        rw [h1, Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_add_distrib,
          Finset.sum_range_sub' (fun i => Pg (ω i)) n, hW]
      have hDs : ∑ k ∈ Finset.range n, Darr n k ω
          = (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, D k ω := by
        rw [Finset.mul_sum]
      rw [hDs, sampleAvg]
      have hlhs : Real.sqrt n * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (ω (k + 1)) - c₀)
          = (Real.sqrt n)⁻¹ * ((∑ k ∈ Finset.range n, f (ω (k + 1))) - (n : ℝ) * c₀) := by
        have s1 : Real.sqrt n * ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (ω (k + 1)) - c₀)
            = (Real.sqrt n * (n : ℝ)⁻¹) * (∑ k ∈ Finset.range n, f (ω (k + 1)))
              - Real.sqrt n * c₀ := by ring
        have s2 : (Real.sqrt n)⁻¹ * ((∑ k ∈ Finset.range n, f (ω (k + 1))) - (n : ℝ) * c₀)
            = (Real.sqrt n)⁻¹ * (∑ k ∈ Finset.range n, f (ω (k + 1)))
              - ((Real.sqrt n)⁻¹ * (n : ℝ)) * c₀ := by ring
        rw [s1, s2, e1, e2]
      rw [hlhs, hsum]
      ring
  refine satisfiesCLT_of_stationary_clt_of_uniformlyErgodic P π huni f hf (σ ^ 2).toNNReal ?_
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ hmart ?_ ?_
  · have hfun : (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - c₀))
        - (fun (n : ℕ) (ω : ℕ → X) => ∑ k ∈ Finset.range n, Darr n k ω)
        = fun (n : ℕ) (ω : ℕ → X) => (Real.sqrt n)⁻¹ * W n ω := by
      funext n ω
      simp only [Pi.sub_apply]
      exact hident n ω
    rw [hfun]
    exact MeasureTheory.tendstoInMeasure_inv_sqrt_mul_of_dominated ν W (fun _ => 2 * C)
      measurable_const hWdom
  · intro n
    exact (measurable_const.mul (((Finset.measurable_sum _
      (fun k _ => hf.comp (measurable_pi_apply (k + 1)))).const_mul _).sub_const _)).aemeasurable
