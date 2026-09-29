-- Prove2me | solution 1 for variance_partialIntegral_le_integral_variance
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T15:26:22.389921+00:00
-- url     : https://prove2.me/submissions/af5e8fd2-de1d-435a-8092-e6794267fd81

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_condExp_comap_fst_eq_partial_integral
import Theorems.Thm_efron_stein_condExp_comap_snd_eq_partial_integral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal BigOperators

/-- **Convexity of variance / conditional-Jensen (two-factor product form).**
For `W ∈ L²(ρ ⊗ σ)` (`ρ`, `σ` probability measures), the `σ`-variance of the `ρ`-average is
bounded by the `ρ`-average of the fiberwise `σ`-variances:

  `variance (fun y => ∫ x, W (x, y) ∂ρ) σ ≤ ∫ x, variance (fun y => W (x, y)) σ ∂ρ`.

This is the centered conditional-Jensen / ANOVA step (`Var(E[·|G]) ≤ E[Var(·|G)]` read as
convexity of variance in the integrand), NOT the false uncentered "single Jensen on the average".
It is the per-step Jensen engine `E[Δ_k²] ≤ E[Var_k]` for the Efron–Stein tensorization.
Source: van Handel, Probability in High Dimension (APC 550), §2.1; Boucheron–Lugosi–Massart,
Concentration Inequalities (OUP 2013), Ch. 3, Theorem 3.1. -/
theorem solution
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ρ : Measure β) [IsProbabilityMeasure ρ] (σ : Measure γ) [IsProbabilityMeasure σ]
    {W : β × γ → ℝ} (hW : MemLp W 2 (ρ.prod σ)) :
    variance (fun y => ∫ x, W (x, y) ∂ρ) σ
      ≤ ∫ x, variance (fun y => W (x, y)) σ ∂ρ := by
  classical
  set u : β → ℝ := fun x => ∫ y, W (x, y) ∂σ with hu_def
  set g : γ → ℝ := fun y => ∫ x, W (x, y) ∂ρ with hg_def
  set m : ℝ := ∫ x, u x ∂ρ with hm_def
  set X : β × γ → ℝ := fun p => W p - u p.1 with hX_def
  let sndMS : MeasurableSpace (β × γ) :=
    MeasurableSpace.comap (Prod.snd : β × γ → γ) (inferInstance : MeasurableSpace γ)
  have hsnd_le : sndMS ≤ Prod.instMeasurableSpace := by
    dsimp [sndMS]
    exact measurable_snd.comap_le
  have hWint : Integrable W (ρ.prod σ) := hW.integrable one_le_two
  have hu_int : Integrable u ρ := by
    simpa [u, hu_def] using hWint.integral_prod_left
  have hg_int : Integrable g σ := by
    simpa [g, hg_def] using hWint.integral_prod_right
  have hu_comp_int : Integrable (fun p : β × γ => u p.1) (ρ.prod σ) :=
    hu_int.comp_fst σ
  have hcond_fst :
      (ρ.prod σ)[W | MeasurableSpace.comap Prod.fst inferInstance]
        =ᵐ[ρ.prod σ] fun p : β × γ => u p.1 := by
    simpa [u, hu_def] using
      condExp_comap_fst_eq_partial_integral ρ σ hWint
  have hu_comp_mem : MemLp (fun p : β × γ => u p.1) 2 (ρ.prod σ) := by
    exact (hW.condExp.ae_eq hcond_fst)
  have hXmem : MemLp X 2 (ρ.prod σ) := by
    simpa [X] using hW.sub hu_comp_mem
  have hXint : Integrable X (ρ.prod σ) := hXmem.integrable one_le_two
  have hXsq_int : Integrable (fun p : β × γ => X p ^ 2) (ρ.prod σ) := by
    simpa [pow_two] using hXmem.integrable_sq
  have hsq_cvx : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) := by
    simpa using (Even.convexOn_pow (𝕜 := ℝ) (n := 2) (by norm_num : Even 2))
  have hsq_lsc : LowerSemicontinuous (fun t : ℝ => t ^ 2) :=
    (continuous_pow 2).lowerSemicontinuous
  have hJ :
      (fun p : β × γ => ((ρ.prod σ)[X | sndMS] p) ^ 2)
        ≤ᵐ[ρ.prod σ] (ρ.prod σ)[(fun p : β × γ => X p ^ 2) | sndMS] := by
    simpa [Function.comp_def, sndMS] using
      hsq_cvx.map_condExp_le_univ
        (μ := ρ.prod σ) (m := sndMS)
        (mα := Prod.instMeasurableSpace)
        hsnd_le hsq_lsc hXint hXsq_int
  have hleft_int : Integrable (fun p : β × γ => ((ρ.prod σ)[X | sndMS] p) ^ 2)
      (ρ.prod σ) := by
    simpa [pow_two] using (hXmem.condExp (m := sndMS)).integrable_sq
  have hright_int : Integrable ((ρ.prod σ)[(fun p : β × γ => X p ^ 2) | sndMS])
      (ρ.prod σ) :=
    integrable_condExp
  have hJ_int :
      ∫ p, ((ρ.prod σ)[X | sndMS] p) ^ 2 ∂(ρ.prod σ)
        ≤ ∫ p, ((ρ.prod σ)[(fun p : β × γ => X p ^ 2) | sndMS]) p ∂(ρ.prod σ) :=
    integral_mono_ae hleft_int hright_int hJ
  have hcond_snd_W :
      (ρ.prod σ)[W | sndMS] =ᵐ[ρ.prod σ] fun p : β × γ => g p.2 := by
    simpa [g, hg_def, sndMS] using
      efron_stein_condExp_comap_snd_eq_partial_integral ρ σ hWint
  have hcond_snd_u :
      (ρ.prod σ)[(fun p : β × γ => u p.1) | sndMS]
        =ᵐ[ρ.prod σ] fun _p : β × γ => m := by
    have hbrick :
        (ρ.prod σ)[(fun p : β × γ => u p.1) | sndMS]
          =ᵐ[ρ.prod σ] fun p : β × γ => ∫ x, (fun q : β × γ => u q.1) (x, p.2) ∂ρ := by
      simpa [sndMS] using
        efron_stein_condExp_comap_snd_eq_partial_integral ρ σ hu_comp_int
    refine hbrick.trans ?_
    exact Filter.Eventually.of_forall (fun p => by simp [m])
  have hcond_snd_X :
      (ρ.prod σ)[X | sndMS] =ᵐ[ρ.prod σ] fun p : β × γ => g p.2 - m := by
    have hXae : X =ᵐ[ρ.prod σ] W - fun p : β × γ => u p.1 := by
      exact Filter.Eventually.of_forall (fun p => by simp [X])
    have hsub := condExp_sub hWint hu_comp_int sndMS
    calc
      (ρ.prod σ)[X | sndMS]
          =ᵐ[ρ.prod σ] (ρ.prod σ)[W - (fun p : β × γ => u p.1) | sndMS] :=
            condExp_congr_ae hXae
      _ =ᵐ[ρ.prod σ] (ρ.prod σ)[W | sndMS]
            - (ρ.prod σ)[(fun p : β × γ => u p.1) | sndMS] := hsub
      _ =ᵐ[ρ.prod σ] fun p : β × γ => g p.2 - m := by
            filter_upwards [hcond_snd_W, hcond_snd_u] with p hWp hup
            simp [hWp, hup]
  have hmean_g : ∫ y, g y ∂σ = m := by
    have hprod₁ : ∫ p, W p ∂(ρ.prod σ) = ∫ x, ∫ y, W (x, y) ∂σ ∂ρ := by
      rw [integral_prod _ hWint]
    have hprod₂ : ∫ p, W p ∂(ρ.prod σ) = ∫ y, ∫ x, W (x, y) ∂ρ ∂σ := by
      rw [integral_prod_symm _ hWint]
    rw [hg_def, hm_def, hu_def]
    rw [← hprod₁, ← hprod₂]
  have hg_sq_int : Integrable (fun y : γ => (g y - m) ^ 2) σ := by
    have hgsq_comp_int : Integrable (fun p : β × γ => (g p.2 - m) ^ 2) (ρ.prod σ) := by
      exact hleft_int.congr (hcond_snd_X.mono fun p hp => by simp [hp])
    exact hgsq_comp_int.of_comp_snd (IsProbabilityMeasure.ne_zero ρ)
  have hleft_eq :
      ∫ p, ((ρ.prod σ)[X | sndMS] p) ^ 2 ∂(ρ.prod σ)
        = variance g σ := by
    calc
      ∫ p, ((ρ.prod σ)[X | sndMS] p) ^ 2 ∂(ρ.prod σ)
          = ∫ p : β × γ, (g p.2 - m) ^ 2 ∂(ρ.prod σ) := by
            exact integral_congr_ae (hcond_snd_X.mono fun p hp => by simp [hp])
      _ = ∫ y, (g y - m) ^ 2 ∂σ := by
            rw [integral_prod_symm _ (hg_sq_int.comp_snd ρ)]
            simp
      _ = variance g σ := by
            rw [variance_eq_integral hg_int.aestronglyMeasurable.aemeasurable, hmean_g]
  have hright_eq :
      ∫ p, ((ρ.prod σ)[(fun p : β × γ => X p ^ 2) | sndMS]) p ∂(ρ.prod σ)
        = ∫ x, variance (fun y => W (x, y)) σ ∂ρ := by
    calc
      ∫ p, ((ρ.prod σ)[(fun p : β × γ => X p ^ 2) | sndMS]) p ∂(ρ.prod σ)
          = ∫ p, X p ^ 2 ∂(ρ.prod σ) := by
            exact integral_condExp hsnd_le
      _ = ∫ x, ∫ y, (W (x, y) - u x) ^ 2 ∂σ ∂ρ := by
            rw [integral_prod _ hXsq_int]
      _ = ∫ x, variance (fun y => W (x, y)) σ ∂ρ := by
            refine integral_congr_ae ?_
            have hW_fib_int : ∀ᵐ x ∂ρ, Integrable (fun y => W (x, y)) σ :=
              hWint.prod_right_ae
            have hWsq_int : Integrable (fun p : β × γ => W p ^ 2) (ρ.prod σ) := by
              simpa [pow_two] using hW.integrable_sq
            have hW_fib_sq : ∀ᵐ x ∂ρ, Integrable (fun y => W (x, y) ^ 2) σ :=
              hWsq_int.prod_right_ae
            filter_upwards [hW_fib_int, hW_fib_sq] with x hx_int hx_sq
            have hx_mem : MemLp (fun y => W (x, y)) 2 σ :=
              (memLp_two_iff_integrable_sq hx_int.aestronglyMeasurable).2 hx_sq
            rw [variance_eq_integral hx_int.aestronglyMeasurable.aemeasurable]
  rw [hleft_eq, hright_eq] at hJ_int
  exact hJ_int

#print axioms solution
