-- Prove2me | solution 1 for MarkovChainCLT.integral_sq_iterKernel_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-16T00:14:29.908295+00:00
-- url     : https://prove2.me/submissions/f1c38fa1-ce5e-4e04-b9aa-587676a97c1b

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Theorems.Thm_MarkovChainCLT_integral_sq_iterKernel_le_of_tvDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

set_option maxHeartbeats 1000000

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : 4 * ρ ≤ 1 / 4)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ ρ)
    (h : X → ℝ) (hh : Measurable h) (hL2 : Integrable (fun x => (h x) ^ 2) π)
    (hmean : ∫ x, h x ∂π = 0) (j : ℕ) :
    ∫ x, (∫ y, h y ∂(iterKernel P (j * N) x)) ^ 2 ∂π
      ≤ (1 / 4 : ℝ) ^ j * ∫ x, (h x) ^ 2 ∂π := by
  classical
  -- `π` is invariant for every power of `P`
  have hinvN : ∀ n : ℕ, (iterKernel P n) ∘ₘ π = π := by
    intro n
    induction n with
    | zero => rw [iterKernel_zero]; simp
    | succ k ih => rw [iterKernel_succ, ← Measure.comp_assoc, ih, hinv]
  have hadd : ∀ a b : ℕ, iterKernel P (a + b) = iterKernel P a ∘ₖ iterKernel P b := by
    intro a b
    induction a with
    | zero => rw [Nat.zero_add, iterKernel_zero, Kernel.id_comp]
    | succ c ih =>
        have h1 : c + 1 + b = (c + b) + 1 := by omega
        rw [h1, iterKernel_succ, ih, ← Kernel.comp_assoc, ← iterKernel_succ]
  -- the two operator facts we iterate
  have hkey : ∀ (u : X → ℝ), Measurable u → Integrable (fun x => (u x) ^ 2) π →
      ∫ x, u x ∂π = 0 → ∀ m : ℕ,
      (Integrable (fun x => (∫ y, u y ∂(iterKernel P m x)) ^ 2) π
        ∧ ∫ x, (∫ y, u y ∂(iterKernel P m x)) ∂π = 0) := by
    intro u hu hu2 hu0 m
    have hcomp : (iterKernel P m) ∘ₘ π = ((iterKernel P m) ∘ₖ Kernel.const Unit π) () :=
      Measure.comp_eq_comp_const_apply
    have hu1 : Integrable u π := by
      refine Integrable.mono' (g := fun x => (1 + (u x) ^ 2) / 2)
        ((integrable_const (1 : ℝ)).add hu2 |>.div_const 2) hu.aestronglyMeasurable ?_
      refine ae_of_all _ (fun x => ?_)
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (|u x| - 1), abs_nonneg (u x), sq_abs (u x)]
    have hsqm : Integrable (fun y => (u y) ^ 2) ((iterKernel P m) ∘ₘ π) := by
      rw [hinvN m]; exact hu2
    have h1m : Integrable u ((iterKernel P m) ∘ₘ π) := by
      rw [hinvN m]; exact hu1
    have hA : Integrable (fun x => ∫ y, (u y) ^ 2 ∂(iterKernel P m x)) π := by
      have := Measure.integrable_integral_norm_of_integrable_comp
        (κ := iterKernel P m) (μ := π) (f := fun y => (u y) ^ 2) hsqm
      refine this.congr ?_
      filter_upwards with x
      refine integral_congr_ae (ae_of_all _ (fun y => ?_))
      simp only
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (u y))]
    have hae : ∀ᵐ x ∂π, Integrable (fun y => (u y) ^ 2) ((iterKernel P m) x) :=
      Measure.ae_integrable_of_integrable_comp hsqm
    have haeu : ∀ᵐ x ∂π, Integrable u ((iterKernel P m) x) :=
      Measure.ae_integrable_of_integrable_comp h1m
    -- Jensen: the square of the average is at most the average of the square
    have hjen : ∀ᵐ x ∂π, (∫ y, u y ∂(iterKernel P m x)) ^ 2
        ≤ ∫ y, (u y) ^ 2 ∂(iterKernel P m x) := by
      filter_upwards [hae, haeu] with x hx hxu
      set c : ℝ := ∫ y, u y ∂(iterKernel P m x) with hc
      have hexp : ∫ y, (u y - c) ^ 2 ∂(iterKernel P m x)
          = (∫ y, (u y) ^ 2 ∂(iterKernel P m x)) - 2 * c * c + c ^ 2 := by
        have hev : ∀ y, (u y - c) ^ 2 = (u y) ^ 2 - 2 * c * u y + c ^ 2 := by
          intro y; ring
        rw [integral_congr_ae (ae_of_all _ hev)]
        have i2 : Integrable (fun y => 2 * c * u y) (iterKernel P m x) := hxu.const_mul (2 * c)
        have i1 : Integrable (fun y => (u y) ^ 2 - 2 * c * u y) (iterKernel P m x) := hx.sub i2
        rw [integral_add i1 (integrable_const (c ^ 2)), integral_sub hx i2,
          integral_const_mul, integral_const]
        simp [Measure.real, ← hc]
      have hnn : 0 ≤ ∫ y, (u y - c) ^ 2 ∂(iterKernel P m x) :=
        integral_nonneg (fun y => sq_nonneg _)
      rw [hexp] at hnn
      nlinarith [hnn]
    constructor
    · refine Integrable.mono' (g := fun x => ∫ y, (u y) ^ 2 ∂(iterKernel P m x)) hA ?_ ?_
      · exact ((hu.stronglyMeasurable.integral_kernel
          (κ := iterKernel P m)).measurable.pow_const 2).aestronglyMeasurable
      · filter_upwards [hjen] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hx
    · have hint : Integrable u (((iterKernel P m) ∘ₖ Kernel.const Unit π) ()) := by
        rw [← hcomp]; exact h1m
      have h1 : ∫ y, u y ∂((iterKernel P m) ∘ₘ π) = ∫ x, (∫ y, u y ∂(iterKernel P m x)) ∂π := by
        rw [hcomp, Kernel.integral_comp hint]
        simp
      rw [← h1, hinvN m, hu0]
  -- the induction, with the function generalised
  have hmain : ∀ (i : ℕ) (u : X → ℝ), Measurable u → Integrable (fun x => (u x) ^ 2) π →
      ∫ x, u x ∂π = 0 →
      ∫ x, (∫ y, u y ∂(iterKernel P (i * N) x)) ^ 2 ∂π
        ≤ (1 / 4 : ℝ) ^ i * ∫ x, (u x) ^ 2 ∂π := by
    intro i
    induction i with
    | zero =>
        intro u hu hu2 hu0
        have hfun : (fun x : X => (∫ y, u y ∂(iterKernel P (0 * N) x)) ^ 2)
            = fun x : X => (u x) ^ 2 := by
          funext x
          rw [Nat.zero_mul, iterKernel_zero, Kernel.id_apply,
            integral_dirac' _ _ hu.stronglyMeasurable]
        rw [hfun]
        simp
    | succ c ih =>
        intro u hu hu2 hu0
        set Pu : X → ℝ := fun x => ∫ y, u y ∂(iterKernel P N x) with hPu
        have hPum : Measurable Pu :=
          (hu.stronglyMeasurable.integral_kernel (κ := iterKernel P N)).measurable
        obtain ⟨hPu2, hPu0⟩ := hkey u hu hu2 hu0 N
        -- one application of the contraction
        have hcontr : ∫ x, (Pu x) ^ 2 ∂π ≤ (1 / 4 : ℝ) * ∫ x, (u x) ^ 2 ∂π := by
          have := integral_sq_iterKernel_le_of_tvDist P π hinv N ρ hρ0 hrate u hu hu2 hu0
          have h2 : (0 : ℝ) ≤ ∫ x, (u x) ^ 2 ∂π := integral_nonneg (fun x => sq_nonneg _)
          nlinarith [this, hρ, h2]
        -- the composition identity, valid almost everywhere
        have hu1 : Integrable u π := by
          refine Integrable.mono' (g := fun x => (1 + (u x) ^ 2) / 2)
            ((integrable_const (1 : ℝ)).add hu2 |>.div_const 2) hu.aestronglyMeasurable ?_
          refine ae_of_all _ (fun x => ?_)
          rw [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|u x| - 1), abs_nonneg (u x), sq_abs (u x)]
        have haeu : ∀ᵐ x ∂π, Integrable u ((iterKernel P ((c + 1) * N)) x) := by
          refine Measure.ae_integrable_of_integrable_comp ?_
          rw [hinvN ((c + 1) * N)]
          exact hu1
        have hidx : (c + 1) * N = N + c * N := by ring
        have hstep : ∀ᵐ x ∂π, ∫ y, u y ∂(iterKernel P ((c + 1) * N) x)
            = ∫ y, Pu y ∂(iterKernel P (c * N) x) := by
          filter_upwards [haeu] with x hx
          have hker : iterKernel P ((c + 1) * N)
              = iterKernel P N ∘ₖ iterKernel P (c * N) := by
            rw [hidx, hadd]
          rw [hker] at hx ⊢
          rw [Kernel.integral_comp hx, hPu]
        have hcongr : ∫ x, (∫ y, u y ∂(iterKernel P ((c + 1) * N) x)) ^ 2 ∂π
            = ∫ x, (∫ y, Pu y ∂(iterKernel P (c * N) x)) ^ 2 ∂π := by
          refine integral_congr_ae ?_
          filter_upwards [hstep] with x hx
          rw [hx]
        rw [hcongr]
        have hIH := ih Pu hPum hPu2 hPu0
        have hq : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ c := by positivity
        calc ∫ x, (∫ y, Pu y ∂(iterKernel P (c * N) x)) ^ 2 ∂π
            ≤ (1 / 4 : ℝ) ^ c * ∫ x, (Pu x) ^ 2 ∂π := hIH
          _ ≤ (1 / 4 : ℝ) ^ c * ((1 / 4 : ℝ) * ∫ x, (u x) ^ 2 ∂π) :=
              mul_le_mul_of_nonneg_left hcontr hq
          _ = (1 / 4 : ℝ) ^ (c + 1) * ∫ x, (u x) ^ 2 ∂π := by ring
  exact hmain j h hh hL2 hmean
