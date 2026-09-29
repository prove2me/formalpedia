-- Prove2me | solution 1 for MarkovChainCLT.summable_covariance_of_bounded_of_summable_alpha
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T01:58:01.233173+00:00
-- url     : https://prove2.me/submissions/894a082a-82b5-4d8e-8e5a-17a256059e16

import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_alpha_cov_bounded
import Theorems.Thm_MarkovChainCLT_stationary_mean_transfer
import Theorems.Thm_MarkovChainCLT_stationary_memLp_transfer

open MeasureTheory ProbabilityTheory MarkovChainCLT Filter
open scoped ProbabilityTheory ENNReal Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) := by
  -- Work at level M := |B|; truncations agree a.e. and inherit zero means.
  have hM0 : (0:ℝ) ≤ |B| := abs_nonneg _
  -- Per-k bound: |∫Y0Y_{k+1}| ≤ 4|B|²·α(k+1).
  have hkey : ∀ k : ℕ, |∫ ω, Y 0 ω * Y (k + 1) ω ∂P|
      ≤ 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1) := by
    intro k
    set T : ℝ → ℝ := fun y => max (-|B|) (min y |B|) with hTdef
    have hTm : Measurable T :=
      (Continuous.max continuous_const
        (continuous_id.min continuous_const)).measurable
    have hTb : ∀ y : ℝ, |T y| ≤ |B| := by
      intro y
      have h1 : -|B| ≤ T y := le_max_left _ _
      have h2 : T y ≤ |B| := by
        apply max_le _ _
        · linarith [abs_nonneg B]
        · exact min_le_right _ _
      exact abs_le.mpr ⟨h1, h2⟩
    set U' : Ω → ℝ := fun ω => T (Y 0 ω) with hU'def
    set V' : Ω → ℝ := fun ω => T (Y (k + 1) ω) with hV'def
    -- Truncations agree a.e. (|Y| < B ≤ |B| a.e. ⇒ trunc = id there).
    have hae0 : U' =ᵐ[P] Y 0 := by
      filter_upwards [hB 0] with ω hω
      show T (Y 0 ω) = Y 0 ω
      have hle : |Y 0 ω| ≤ |B| := le_trans hω.le (le_abs_self B)
      have h1 : min (Y 0 ω) |B| = Y 0 ω := min_eq_left (abs_le.mp hle).2
      have h2 : max (-|B|) (Y 0 ω) = Y 0 ω :=
        max_eq_right (by linarith [(abs_le.mp hle).1])
      show max (-|B|) (min (Y 0 ω) |B|) = Y 0 ω
      rw [h1]
      exact h2
    have hae1 : V' =ᵐ[P] Y (k + 1) := by
      filter_upwards [hB (k + 1)] with ω hω
      show T (Y (k + 1) ω) = Y (k + 1) ω
      have hle : |Y (k + 1) ω| ≤ |B| := le_trans hω.le (le_abs_self B)
      have h1 : min (Y (k + 1) ω) |B| = Y (k + 1) ω :=
        min_eq_left (abs_le.mp hle).2
      have h2 : max (-|B|) (Y (k + 1) ω) = Y (k + 1) ω :=
        max_eq_right (by linarith [(abs_le.mp hle).1])
      show max (-|B|) (min (Y (k + 1) ω) |B|) = Y (k + 1) ω
      rw [h1]
      exact h2
    -- Truncations inherit zero means via a.e. equality.
    have hEU' : ∫ ω, U' ω ∂P = 0 := by
      have e : (∫ ω, U' ω ∂P) = ∫ ω, Y 0 ω ∂P :=
        integral_congr_ae hae0
      rw [e]
      exact hcent
    have hEV' : ∫ ω, V' ω ∂P = 0 := by
      have e : (∫ ω, V' ω ∂P) = ∫ ω, Y (k + 1) ω ∂P :=
        integral_congr_ae hae1
      rw [e]
      exact MarkovChainCLT.stationary_mean_transfer P Y hY hstat hcent (k + 1)
    -- L² via everywhere-boundedness on a probability space.
    have hTm : Measurable T :=
      (Continuous.max continuous_const
        (continuous_id.min continuous_const)).measurable
    have hU'm : Measurable U' := hTm.comp (hY 0)
    have hV'm : Measurable V' := hTm.comp (hY (k + 1))
    have hU'L2 : MemLp U' 2 P :=
      MemLp.of_bound hU'm.aestronglyMeasurable _ (by
        filter_upwards with ω
        calc ‖U' ω‖ = |U' ω| := Real.norm_eq_abs _
          _ ≤ |B| := hTb _)
    have hV'L2 : MemLp V' 2 P :=
      MemLp.of_bound hV'm.aestronglyMeasurable _ (by
        filter_upwards with ω
        calc ‖V' ω‖ = |V' ω| := Real.norm_eq_abs _
          _ ≤ |B| := hTb _)
    -- Past/future exact measurability for the bounded lemma (lag k+1 at j=0).
    -- (Lattice facts inlined: the platform copies live in the wrong env.)
    have hcoord_past : Measurable[processSigma Y (Set.Iic 0)] (Y 0) := by
      refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
      exact le_iSup₂ (f := fun i (_ : i ∈ Set.Iic 0) =>
        MeasurableSpace.comap (Y i) inferInstance) 0 (Set.mem_Iic.2 le_rfl)
    have hcoord_fut : Measurable[processSigma Y (Set.Ici (k + 1))] (Y (k + 1)) := by
      refine (measurable_iff_comap_le.2 le_rfl).mono ?_ le_rfl
      refine le_iSup₂ (f := fun i (_ : i ∈ Set.Ici (k + 1)) =>
        MeasurableSpace.comap (Y i) inferInstance) (k + 1) ?_
      simp
    have hU'past : Measurable[processSigma Y (Set.Iic 0)] U' :=
      hTm.comp hcoord_past
    have hV'fut : Measurable[processSigma Y (Set.Ici (0 + (k + 1)))] V' := by
      have h : Measurable[processSigma Y (Set.Ici (k + 1))] V' :=
        hTm.comp hcoord_fut
      have e : (0 : ℕ) + (k + 1) = k + 1 := Nat.zero_add _
      rw [e]
      exact h
    -- Chain: plain = trunc integral = cov = bounded.
    have hInt : (∫ ω, Y 0 ω * Y (k + 1) ω ∂P)
        = ∫ ω, U' ω * V' ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hae0, hae1] with ω h0 h1
      rw [h0, h1]
    have hCov : (∫ ω, U' ω * V' ω ∂P) = cov[U', V'; P] := by
      have h := covariance_eq_sub hU'L2 hV'L2
      rw [hEU', hEV', mul_zero, sub_zero] at h
      exact h.symm
    calc |∫ ω, Y 0 ω * Y (k + 1) ω ∂P| = |cov[U', V'; P]| := by
          rw [hInt, hCov]
      _ ≤ 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1) := by
          have hU'b : ∀ ω, |U' ω| ≤ |B| := fun ω => hTb (Y 0 ω)
          have hV'b : ∀ ω, |V' ω| ≤ |B| := fun ω => hTb (Y (k + 1) ω)
          exact MarkovChainCLT.alpha_cov_bounded P Y hY (k + 1) 0 U' V'
            hU'past hV'fut _ (abs_nonneg _) hU'b hV'b
  -- Comparison with the summable α series.
  have hsum : Summable (fun k : ℕ => 4 * |B| ^ 2 * alphaMixingCoef P Y (k + 1)) :=
    ((summable_nat_add_iff 1).2 hα).mul_left _
  exact Summable.of_norm_bounded hsum fun k => by simpa using hkey k
