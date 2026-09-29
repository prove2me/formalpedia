-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_quadVar_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:42:07.198191+00:00
-- url     : https://prove2.me/submissions/b08d7daa-3f8f-4db5-9113-b8960539d22f

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_integral_sq_sampleAvg_sub_le
import Theorems.Thm_MarkovChainCLT_integral_sq_sum_weighted_mds_le
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (huni : UniformlyErgodic P π) (lam : Measure X) [IsProbabilityMeasure lam]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      ∫ ω, ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1)) - ∫ y, g y ∂(P (ω k))) ^ 2
            - (∫ x, (g x) ^ 2 ∂π - ∫ x, (∫ y, g y ∂(P x)) ^ 2 ∂π)) ^ 2
          ∂(chainMeasure P lam) ≤ K / n := by
  classical
  have hC0 : 0 ≤ C := by
    rcases isEmpty_or_nonempty X with hX | hX
    · have h1 : lam Set.univ = 1 := measure_univ
      rw [Set.univ_eq_empty_iff.mpr hX, measure_empty] at h1
      exact absurd h1 zero_ne_one
    · exact le_trans (abs_nonneg _) (hC hX.some)
  set ν : Measure (ℕ → X) := chainMeasure P lam with hν
  set Pg : X → ℝ := fun x => ∫ y, g y ∂(P x) with hPg
  have hPgm : Measurable Pg := (hg.stronglyMeasurable.integral_kernel (κ := P)).measurable
  have hPgC : ∀ x, |Pg x| ≤ C := by
    intro x
    rw [hPg]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun y => |g y|) (P x) :=
      ⟨(continuous_abs.measurable.comp hg).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun z => by simpa using hC z))⟩
    have h2 := integral_mono h1 (integrable_const C) (fun z => hC z)
    simpa using h2
  -- three bounded observables
  have hg2m : Measurable (fun x => (g x) ^ 2) := hg.pow_const 2
  have hg2C : ∀ x, |(g x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hC x, abs_nonneg (g x), sq_abs (g x)]
  have hPg2m : Measurable (fun x => (Pg x) ^ 2) := hPgm.pow_const 2
  have hPg2C : ∀ x, |(Pg x) ^ 2| ≤ C ^ 2 := by
    intro x
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hPgC x, abs_nonneg (Pg x), sq_abs (Pg x)]
  obtain ⟨K1, hK10, hK1⟩ :=
    integral_sq_sampleAvg_sub_le P π huni lam (fun x => (g x) ^ 2) hg2m (C ^ 2) hg2C
  obtain ⟨K2, hK20, hK2⟩ :=
    integral_sq_sampleAvg_sub_le P π huni lam (fun x => (Pg x) ^ 2) hPg2m (C ^ 2) hPg2C
  refine ⟨3 * K1 + 3 * K2 + 30 * (2 * C ^ 2) ^ 2, by positivity, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set a₁ : ℝ := ∫ x, (g x) ^ 2 ∂π with ha₁
  set a₂ : ℝ := ∫ x, (Pg x) ^ 2 ∂π with ha₂
  set A : (ℕ → X) → ℝ :=
    fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1))) ^ 2 - a₁ with hA
  set Bm : (ℕ → X) → ℝ :=
    fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (Pg (ω (k + 1))) ^ 2 - a₂ with hBm
  set T : (ℕ → X) → ℝ :=
    fun ω => (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n,
      Pg (ω k) * (g (ω (k + 1)) - Pg (ω k)) with hT
  set R : (ℕ → X) → ℝ :=
    fun ω => (n : ℝ)⁻¹ * ((Pg (ω n)) ^ 2 - (Pg (ω 0)) ^ 2) with hR
  -- the algebraic decomposition of the quadratic variation
  have hdec : ∀ ω : ℕ → X,
      (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1)) - Pg (ω k)) ^ 2 - (a₁ - a₂)
        = A ω - 2 * T ω - Bm ω + R ω := by
    intro ω
    have hpt : ∀ k, (g (ω (k + 1)) - Pg (ω k)) ^ 2
        = (g (ω (k + 1))) ^ 2 - 2 * (Pg (ω k) * (g (ω (k + 1)) - Pg (ω k)))
          - (Pg (ω k)) ^ 2 := by
      intro k
      ring
    have hshift : ∑ k ∈ Finset.range n, (Pg (ω k)) ^ 2
        = (∑ k ∈ Finset.range n, (Pg (ω (k + 1))) ^ 2)
          + ((Pg (ω 0)) ^ 2 - (Pg (ω n)) ^ 2) := by
      have h2 : (∑ k ∈ Finset.range n, (Pg (ω k)) ^ 2)
          - (∑ k ∈ Finset.range n, (Pg (ω (k + 1))) ^ 2)
          = (Pg (ω 0)) ^ 2 - (Pg (ω n)) ^ 2 := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_range_sub' (fun i => (Pg (ω i)) ^ 2) n
      linarith
    rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hshift, hA, hBm, hT, hR]
    field_simp
    ring
  -- pointwise bound by three squares
  have hquad : ∀ ω : ℕ → X,
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1)) - Pg (ω k)) ^ 2 - (a₁ - a₂)) ^ 2
        ≤ 3 * (A ω) ^ 2 + 3 * (Bm ω) ^ 2 + 3 * (2 * T ω - R ω) ^ 2 := by
    intro ω
    rw [hdec ω]
    nlinarith [sq_nonneg (A ω + Bm ω), sq_nonneg (A ω - R ω + 2 * T ω),
      sq_nonneg (Bm ω + R ω - 2 * T ω)]
  -- pointwise bounds on the four pieces
  have hgen : ∀ (F : (ℕ → X) → ℝ), Measurable F → ∀ M : ℝ, (∀ ω, |F ω| ≤ M) →
      Integrable (fun ω => (F ω) ^ 2) ν := by
    intro F hF M hM
    refine ⟨(hF.pow_const 2).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := M ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hM ω, abs_nonneg (F ω), sq_abs (F ω)]
  have hsumbd : ∀ (u : X → ℝ), (∀ x, |u x| ≤ C ^ 2) → ∀ ω : ℕ → X,
      |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, u (ω (k + 1))| ≤ C ^ 2 := by
    intro u hu ω
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹), inv_mul_le_iff₀ hnR]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ k ∈ Finset.range n, |u (ω (k + 1))| ≤ ∑ _k ∈ Finset.range n, C ^ 2 :=
          Finset.sum_le_sum (fun k _ => hu _)
      _ = n * C ^ 2 := by simp [Finset.sum_const, Finset.card_range]
  have ha₁C : |a₁| ≤ C ^ 2 := by
    rw [ha₁]
    refine le_trans abs_integral_le_integral_abs ?_
    have hi : Integrable (fun y => |(g y) ^ 2|) π :=
      ⟨(continuous_abs.measurable.comp hg2m).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C ^ 2)
          (ae_of_all _ (fun z => by simpa using hg2C z))⟩
    have := integral_mono hi (integrable_const (C ^ 2)) (fun z => hg2C z)
    simpa using this
  have ha₂C : |a₂| ≤ C ^ 2 := by
    rw [ha₂]
    refine le_trans abs_integral_le_integral_abs ?_
    have hi : Integrable (fun y => |(Pg y) ^ 2|) π :=
      ⟨(continuous_abs.measurable.comp hPg2m).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C ^ 2)
          (ae_of_all _ (fun z => by simpa using hPg2C z))⟩
    have := integral_mono hi (integrable_const (C ^ 2)) (fun z => hPg2C z)
    simpa using this
  have hAbd : ∀ ω, |A ω| ≤ 2 * C ^ 2 := by
    intro ω
    calc |A ω| ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1))) ^ 2| + |a₁| := abs_sub _ _
      _ ≤ 2 * C ^ 2 := by
          have := hsumbd (fun x => (g x) ^ 2) hg2C ω
          linarith
  have hBbd : ∀ ω, |Bm ω| ≤ 2 * C ^ 2 := by
    intro ω
    calc |Bm ω| ≤ |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (Pg (ω (k + 1))) ^ 2| + |a₂| :=
          abs_sub _ _
      _ ≤ 2 * C ^ 2 := by
          have := hsumbd (fun x => (Pg x) ^ 2) hPg2C ω
          linarith
  have hRbd : ∀ ω, |R ω| ≤ 2 * C ^ 2 := by
    intro ω
    rw [hR, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹), inv_mul_le_iff₀ hnR]
    have h1 : |(Pg (ω n)) ^ 2 - (Pg (ω 0)) ^ 2| ≤ 2 * C ^ 2 := by
      calc |(Pg (ω n)) ^ 2 - (Pg (ω 0)) ^ 2| ≤ |(Pg (ω n)) ^ 2| + |(Pg (ω 0)) ^ 2| :=
            abs_sub _ _
        _ ≤ 2 * C ^ 2 := by linarith [hPg2C (ω n), hPg2C (ω 0)]
    nlinarith [hn1, sq_nonneg C]
  have hTbd : ∀ ω, |T ω| ≤ 2 * C ^ 2 := by
    intro ω
    rw [hT, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹), inv_mul_le_iff₀ hnR]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ Finset.range n, |Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))| ≤ 2 * C ^ 2 := by
      intro k _
      rw [abs_mul]
      have h1 : |g (ω (k + 1)) - Pg (ω k)| ≤ 2 * C := by
        calc |g (ω (k + 1)) - Pg (ω k)| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
          _ ≤ 2 * C := by linarith [hC (ω (k + 1)), hPgC (ω k)]
      nlinarith [hPgC (ω k), abs_nonneg (Pg (ω k)), abs_nonneg (g (ω (k + 1)) - Pg (ω k))]
    calc ∑ k ∈ Finset.range n, |Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))|
        ≤ ∑ _k ∈ Finset.range n, 2 * C ^ 2 := Finset.sum_le_sum hterm
      _ = n * (2 * C ^ 2) := by simp [Finset.sum_const, Finset.card_range]
  -- measurability of the four pieces
  have hAm : Measurable A :=
    ((Finset.measurable_sum _
      (fun k _ => (hg.comp (measurable_pi_apply (k + 1))).pow_const 2)).const_mul _).sub_const _
  have hBmm : Measurable Bm :=
    ((Finset.measurable_sum _
      (fun k _ => (hPgm.comp (measurable_pi_apply (k + 1))).pow_const 2)).const_mul _).sub_const _
  have hTm : Measurable T :=
    (Finset.measurable_sum _ (fun k _ => (hPgm.comp (measurable_pi_apply k)).mul
      ((hg.comp (measurable_pi_apply (k + 1))).sub
        (hPgm.comp (measurable_pi_apply k))))).const_mul _
  have hRm : Measurable R :=
    (((hPgm.comp (measurable_pi_apply n)).pow_const 2).sub
      ((hPgm.comp (measurable_pi_apply 0)).pow_const 2)).const_mul _
  -- the three integral bounds
  have hA2 : ∫ ω, (A ω) ^ 2 ∂ν ≤ K1 / n := hK1 n hn
  have hB2 : ∫ ω, (Bm ω) ^ 2 ∂ν ≤ K2 / n := hK2 n hn
  have hT2 : ∫ ω, (T ω) ^ 2 ∂ν ≤ (2 * C ^ 2) ^ 2 / n := by
    have hw := integral_sq_sum_weighted_mds_le P lam g hg C hC Pg hPgm C hPgC n
    have hsm : Measurable (fun ω : ℕ → X => ∑ k ∈ Finset.range n,
        Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))) :=
      Finset.measurable_sum _ (fun k _ => (hPgm.comp (measurable_pi_apply k)).mul
        ((hg.comp (measurable_pi_apply (k + 1))).sub (hPgm.comp (measurable_pi_apply k))))
    have hint : Integrable (fun ω : ℕ → X => (∑ k ∈ Finset.range n,
        Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))) ^ 2) ν :=
      hgen _ hsm (n * (2 * C ^ 2)) (fun ω => by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        have hterm : ∀ k ∈ Finset.range n,
            |Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))| ≤ 2 * C ^ 2 := by
          intro k _
          rw [abs_mul]
          have h1 : |g (ω (k + 1)) - Pg (ω k)| ≤ 2 * C := by
            calc |g (ω (k + 1)) - Pg (ω k)| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
              _ ≤ 2 * C := by linarith [hC (ω (k + 1)), hPgC (ω k)]
          nlinarith [hPgC (ω k), abs_nonneg (Pg (ω k)),
            abs_nonneg (g (ω (k + 1)) - Pg (ω k))]
        calc ∑ k ∈ Finset.range n, |Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))|
            ≤ ∑ _k ∈ Finset.range n, 2 * C ^ 2 := Finset.sum_le_sum hterm
          _ = n * (2 * C ^ 2) := by simp [Finset.sum_const, Finset.card_range])
    have hpull : ∫ ω, (T ω) ^ 2 ∂ν
        = ((n : ℝ)⁻¹) ^ 2 * ∫ ω, (∑ k ∈ Finset.range n,
            Pg (ω k) * (g (ω (k + 1)) - Pg (ω k))) ^ 2 ∂ν := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ (fun ω => ?_))
      rw [hT]
      ring
    rw [hpull]
    have hnn : (0:ℝ) ≤ ((n : ℝ)⁻¹) ^ 2 := sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_left hw hnn
    refine le_trans h2 ?_
    rw [div_eq_mul_inv]
    have e1 : ((n : ℝ)⁻¹) ^ 2 * ((n : ℝ) * (C * (2 * C)) ^ 2)
        = (n : ℝ)⁻¹ * (C * (2 * C)) ^ 2 := by field_simp
    rw [e1]
    have e2 : (C * (2 * C)) ^ 2 = (2 * C ^ 2) ^ 2 := by ring
    rw [e2]
    ring_nf
    exact le_refl _
  have hR2 : ∫ ω, (R ω) ^ 2 ∂ν ≤ (2 * C ^ 2) ^ 2 / n := by
    have hbd : ∀ ω, (R ω) ^ 2 ≤ (2 * C ^ 2) ^ 2 / n := by
      intro ω
      have h1 : |R ω| ≤ (2 * C ^ 2) * (n : ℝ)⁻¹ := by
        rw [hR, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
        have h2 : |(Pg (ω n)) ^ 2 - (Pg (ω 0)) ^ 2| ≤ 2 * C ^ 2 := by
          calc |(Pg (ω n)) ^ 2 - (Pg (ω 0)) ^ 2| ≤ |(Pg (ω n)) ^ 2| + |(Pg (ω 0)) ^ 2| :=
                abs_sub _ _
            _ ≤ 2 * C ^ 2 := by linarith [hPg2C (ω n), hPg2C (ω 0)]
        nlinarith [h2, (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
      have hipos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
      have hmul : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hnR)
      have hinv : (n : ℝ)⁻¹ ≤ 1 := by nlinarith [hmul, hipos, hn1]
      have hsq : (R ω) ^ 2 ≤ ((2 * C ^ 2) * (n : ℝ)⁻¹) ^ 2 := by
        nlinarith [abs_nonneg (R ω), sq_abs (R ω), h1,
          mul_nonneg (by positivity : (0:ℝ) ≤ 2 * C ^ 2) hipos.le]
      rw [div_eq_mul_inv]
      nlinarith [hsq, hinv, hipos, sq_nonneg (2 * C ^ 2),
        mul_nonneg (sq_nonneg (2 * C ^ 2)) hipos.le]
    calc ∫ ω, (R ω) ^ 2 ∂ν ≤ ∫ _ω : ℕ → X, (2 * C ^ 2) ^ 2 / n ∂ν :=
          integral_mono (hgen R hRm (2 * C ^ 2) hRbd) (integrable_const _) hbd
      _ = (2 * C ^ 2) ^ 2 / n := by simp
  -- combine
  have hTRbd : ∀ ω, |2 * T ω - R ω| ≤ 6 * C ^ 2 := by
    intro ω
    calc |2 * T ω - R ω| ≤ |2 * T ω| + |R ω| := abs_sub _ _
      _ ≤ 6 * C ^ 2 := by
          rw [abs_mul]
          simp only [abs_two]
          linarith [hTbd ω, hRbd ω]
  have hTR2 : ∫ ω, (2 * T ω - R ω) ^ 2 ∂ν ≤ 10 * (2 * C ^ 2) ^ 2 / n := by
    have hpt2 : ∀ ω, (2 * T ω - R ω) ^ 2 ≤ 8 * (T ω) ^ 2 + 2 * (R ω) ^ 2 := by
      intro ω
      nlinarith [sq_nonneg (2 * T ω + R ω)]
    have hint1 : Integrable (fun ω => (T ω) ^ 2) ν := hgen T hTm (2 * C ^ 2) hTbd
    have hint2 : Integrable (fun ω => (R ω) ^ 2) ν := hgen R hRm (2 * C ^ 2) hRbd
    have hlhs : Integrable (fun ω => (2 * T ω - R ω) ^ 2) ν :=
      hgen (fun ω => 2 * T ω - R ω) ((hTm.const_mul 2).sub hRm) (6 * C ^ 2) hTRbd
    have hi1 : Integrable (fun ω : ℕ → X => 8 * (T ω) ^ 2) ν := hint1.const_mul 8
    have hi2 : Integrable (fun ω : ℕ → X => 2 * (R ω) ^ 2) ν := hint2.const_mul 2
    have := integral_mono hlhs (hi1.add hi2) hpt2
    simp only [Pi.add_apply] at this
    rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul] at this
    have h8 := mul_le_mul_of_nonneg_left hT2 (by norm_num : (0:ℝ) ≤ 8)
    have h2 := mul_le_mul_of_nonneg_left hR2 (by norm_num : (0:ℝ) ≤ 2)
    have e : (8 : ℝ) * ((2 * C ^ 2) ^ 2 / n) + 2 * ((2 * C ^ 2) ^ 2 / n)
        = 10 * (2 * C ^ 2) ^ 2 / n := by ring
    linarith
  have hlhsint : Integrable (fun ω : ℕ → X =>
      ((n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, (g (ω (k + 1)) - Pg (ω k)) ^ 2 - (a₁ - a₂)) ^ 2) ν := by
    refine hgen _ ?_ (10 * C ^ 2) (fun ω => ?_)
    · exact ((Finset.measurable_sum _ (fun k _ =>
        ((hg.comp (measurable_pi_apply (k + 1))).sub
          (hPgm.comp (measurable_pi_apply k))).pow_const 2)).const_mul _).sub_const _
    · rw [hdec ω]
      have h2T : |2 * T ω| = 2 * |T ω| := by
        rw [abs_mul, abs_two]
      calc |A ω - 2 * T ω - Bm ω + R ω|
          ≤ |A ω - 2 * T ω - Bm ω| + |R ω| := abs_add_le _ _
        _ ≤ (|A ω - 2 * T ω| + |Bm ω|) + |R ω| := by
            linarith [abs_sub (A ω - 2 * T ω) (Bm ω)]
        _ ≤ ((|A ω| + |2 * T ω|) + |Bm ω|) + |R ω| := by
            linarith [abs_sub (A ω) (2 * T ω)]
        _ ≤ 10 * C ^ 2 := by
            rw [h2T]
            linarith [hAbd ω, hBbd ω, hRbd ω, hTbd ω]
  have hj1 : Integrable (fun ω : ℕ → X => 3 * (A ω) ^ 2) ν :=
    (hgen A hAm (2 * C ^ 2) hAbd).const_mul 3
  have hj2 : Integrable (fun ω : ℕ → X => 3 * (Bm ω) ^ 2) ν :=
    (hgen Bm hBmm (2 * C ^ 2) hBbd).const_mul 3
  have hj3 : Integrable (fun ω : ℕ → X => 3 * (2 * T ω - R ω) ^ 2) ν :=
    (hgen (fun ω => 2 * T ω - R ω) ((hTm.const_mul 2).sub hRm) (6 * C ^ 2) hTRbd).const_mul 3
  have hj12 : Integrable (fun ω : ℕ → X => 3 * (A ω) ^ 2 + 3 * (Bm ω) ^ 2) ν := hj1.add hj2
  have hmain := integral_mono hlhsint (hj12.add hj3) hquad
  simp only [Pi.add_apply] at hmain
  rw [integral_add hj12 hj3, integral_add hj1 hj2,
    integral_const_mul, integral_const_mul, integral_const_mul] at hmain
  have hfin : (3 : ℝ) * (K1 / n) + 3 * (K2 / n) + 3 * (10 * (2 * C ^ 2) ^ 2 / n)
      = (3 * K1 + 3 * K2 + 30 * (2 * C ^ 2) ^ 2) / n := by ring
  have h3A := mul_le_mul_of_nonneg_left hA2 (by norm_num : (0:ℝ) ≤ 3)
  have h3B := mul_le_mul_of_nonneg_left hB2 (by norm_num : (0:ℝ) ≤ 3)
  have h3T := mul_le_mul_of_nonneg_left hTR2 (by norm_num : (0:ℝ) ≤ 3)
  linarith [hmain, h3A, h3B, h3T]
