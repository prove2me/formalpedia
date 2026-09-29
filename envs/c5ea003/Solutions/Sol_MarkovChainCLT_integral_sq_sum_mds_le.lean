-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_sum_mds_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T23:21:57.040075+00:00
-- url     : https://prove2.me/submissions/9c63c39b-7a12-4f42-b41e-1c0c1b8f0240

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel
import Theorems.Thm_MarkovChainCLT_condExp_next_coord
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder
  ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 2000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) (n : ℕ) :
    ∫ ω, (∑ k ∈ Finset.range n, (g (ω (k + 1)) - ∫ y, g y ∂(P (ω k)))) ^ 2
        ∂(chainMeasure P lam)
      ≤ n * (2 * C) ^ 2 := by
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
  have hPgB : ∀ x, |Pg x| ≤ C := by
    intro x
    rw [hPg]
    refine le_trans abs_integral_le_integral_abs ?_
    have h1 : Integrable (fun y => |g y|) (P x) :=
      ⟨(continuous_abs.measurable.comp hg).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun z => by simpa using hC z))⟩
    have h2 := integral_mono h1 (integrable_const C) (fun z => hC z)
    simpa using h2
  set D : ℕ → (ℕ → X) → ℝ := fun k ω => g (ω (k + 1)) - Pg (ω k) with hD
  have hDm : ∀ k, Measurable (D k) := by
    intro k
    exact (hg.comp (measurable_pi_apply (k + 1))).sub (hPgm.comp (measurable_pi_apply k))
  have hDB : ∀ k ω, |D k ω| ≤ 2 * C := by
    intro k ω
    calc |D k ω| ≤ |g (ω (k + 1))| + |Pg (ω k)| := abs_sub _ _
      _ ≤ 2 * C := by linarith [hC (ω (k + 1)), hPgB (ω k)]
  have hDint : ∀ k, Integrable (D k) ν :=
    fun k => ⟨(hDm k).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := 2 * C)
        (ae_of_all _ (fun ω => by simpa using hDB k ω))⟩
  have hprodint : ∀ j k, Integrable (fun ω => D j ω * D k ω) ν := by
    intro j k
    refine ⟨((hDm j).mul (hDm k)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := (2 * C) ^ 2) (ae_of_all _ (fun ω => ?_))⟩
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [hDB j ω, hDB k ω, abs_nonneg (D j ω), abs_nonneg (D k ω)]
  -- orthogonality of the martingale differences
  have horth : ∀ j k : ℕ, j < k → ∫ ω, D j ω * D k ω ∂ν = 0 := by
    intro j k hjk
    have hmle : MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k) inferInstance
        ≤ (inferInstance : MeasurableSpace (ℕ → X)) := (measurable_frestrictLe k).comap_le
    haveI : IsFiniteMeasure (ν.trim hmle) := isFiniteMeasure_trim hmle
    have hcoordm : ∀ i : ℕ, i ≤ k → Measurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] (fun ω : ℕ → X => ω i) := by
      intro i hi
      have h1 : Measurable[MeasurableSpace.comap (frestrictLe (π := fun _ : ℕ => X) k)
          inferInstance] (frestrictLe (π := fun _ : ℕ => X) k) := Measurable.of_comap_le le_rfl
      have h2 := (measurable_pi_apply (⟨i, Finset.mem_Iic.2 hi⟩ : Finset.Iic k)).comp h1
      exact h2
    have hDjm : StronglyMeasurable[MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] (D j) :=
      ((hg.comp (hcoordm (j + 1) (by omega))).sub
        (hPgm.comp (hcoordm j (by omega)))).stronglyMeasurable
    have hint1 : Integrable (fun ω : ℕ → X => g (ω (k + 1))) ν :=
      ⟨(hg.comp (measurable_pi_apply (k + 1))).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun ω => by simpa using hC _))⟩
    have hint2 : Integrable (fun ω : ℕ → X => Pg (ω k)) ν :=
      ⟨(hPgm.comp (measurable_pi_apply k)).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (C := C) (ae_of_all _ (fun ω => by simpa using hPgB _))⟩
    have hcond : ν[D k | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] =ᵐ[ν] 0 := by
      have h1 := (condExp_next_coord P lam g hg C hC k).symm
      have hsmPg : StronglyMeasurable[MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
          (fun ω : ℕ → X => Pg (ω k)) := by
        have hx := hPgm.comp (hcoordm k le_rfl)
        exact hx.stronglyMeasurable
      have h2 : ν[fun ω : ℕ → X => Pg (ω k) | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
          =ᵐ[ν] fun ω : ℕ → X => Pg (ω k) := by
        rw [condExp_of_stronglyMeasurable hmle hsmPg hint2]
      have h3 : ν[D k | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
          =ᵐ[ν] ν[fun ω : ℕ → X => g (ω (k + 1)) | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
            - ν[fun ω : ℕ → X => Pg (ω k) | MeasurableSpace.comap
              (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] :=
        condExp_sub hint1 hint2 _
      filter_upwards [h1, h2, h3] with ω e1 e2 e3
      have e3' : (ν[D k | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω
          = (ν[fun ω : ℕ → X => g (ω (k + 1)) | MeasurableSpace.comap
              (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω
            - (ν[fun ω : ℕ → X => Pg (ω k) | MeasurableSpace.comap
              (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω := by
        rw [e3]
        rfl
      show (ν[D k | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω = 0
      rw [e3', e1, e2]
      simp [hPg]
    have hpull : ν[fun ω => D j ω * D k ω | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]
        =ᵐ[ν] (D j) * ν[D k | MeasurableSpace.comap
          (frestrictLe (π := fun _ : ℕ => X) k) inferInstance] :=
      condExp_mul_of_stronglyMeasurable_left hDjm (hprodint j k) (hDint k)
    have hfin : (fun ω => (D j ω) * (ν[D k | MeasurableSpace.comap
        (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω) =ᵐ[ν] fun _ => (0 : ℝ) := by
      filter_upwards [hcond] with ω e
      simp only [Pi.zero_apply] at e
      rw [e, mul_zero]
    calc ∫ ω, D j ω * D k ω ∂ν
        = ∫ ω, (ν[fun ω => D j ω * D k ω | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω ∂ν :=
          (integral_condExp hmle).symm
      _ = ∫ ω, (D j ω) * (ν[D k | MeasurableSpace.comap
            (frestrictLe (π := fun _ : ℕ => X) k) inferInstance]) ω ∂ν :=
          integral_congr_ae hpull
      _ = 0 := by rw [integral_congr_ae hfin, integral_zero]
  -- expand the square and cancel the off-diagonal terms
  show ∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂ν ≤ n * (2 * C) ^ 2
  have hsq : ∀ ω : ℕ → X, (∑ k ∈ Finset.range n, D k ω) ^ 2
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, D j ω * D k ω := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hgoal : ∫ ω, (∑ k ∈ Finset.range n, D k ω) ^ 2 ∂ν
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, ∫ ω, D j ω * D k ω ∂ν := by
    rw [integral_congr_ae (ae_of_all _ hsq),
      integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hprodint j k))]
    exact Finset.sum_congr rfl (fun j _ => integral_finset_sum _ (fun k _ => hprodint j k))
  have hdiag : ∀ j ∈ Finset.range n,
      (∑ k ∈ Finset.range n, ∫ ω, D j ω * D k ω ∂ν) = ∫ ω, D j ω * D j ω ∂ν := by
    intro j hj
    refine Finset.sum_eq_single j (fun k _ hkj => ?_) (fun hjn => absurd hj hjn)
    rcases lt_or_gt_of_ne hkj with hlt | hgt
    · calc ∫ ω, D j ω * D k ω ∂ν = ∫ ω, D k ω * D j ω ∂ν := by
            simp only [mul_comm]
        _ = 0 := horth k j hlt
    · exact horth j k hgt
  have hbd : ∀ j, ∫ ω, D j ω * D j ω ∂ν ≤ (2 * C) ^ 2 := by
    intro j
    have h1 : ∀ ω, D j ω * D j ω ≤ (2 * C) ^ 2 := by
      intro ω
      nlinarith [hDB j ω, abs_nonneg (D j ω), sq_abs (D j ω)]
    calc ∫ ω, D j ω * D j ω ∂ν ≤ ∫ _ω : ℕ → X, (2 * C) ^ 2 ∂ν :=
          integral_mono (hprodint j j) (integrable_const _) h1
      _ = (2 * C) ^ 2 := by simp
  rw [hgoal]
  calc ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, ∫ ω, D j ω * D k ω ∂ν
      = ∑ j ∈ Finset.range n, ∫ ω, D j ω * D j ω ∂ν := Finset.sum_congr rfl hdiag
    _ ≤ ∑ _j ∈ Finset.range n, (2 * C) ^ 2 := Finset.sum_le_sum (fun j _ => hbd j)
    _ = n * (2 * C) ^ 2 := by simp [Finset.sum_const, Finset.card_range]
