-- Prove2me | solution 1 for AbelianTargets.exists_anisotropic_scales
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-19T04:12:29.290989+00:00
-- url     : https://prove2.me/submissions/f4bc53d3-da10-4f22-9747-8669d6c76dc2

import Init
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic.Linarith

set_option autoImplicit false

-- Preserved source skeleton: AbelianTargets.AnisotropicScales
section
/-!
# Successive scale choice in Proposition 6.1

After the first scale is chosen, an arbitrary finite transverse bound
depending on that scale can be made small by a second scale. No uniform
bound in the first scale is assumed or needed.
-/

namespace AbelianTargets

open Filter Topology

theorem logarithmic_scale_error_tendsto :
    Tendsto (fun L : ℕ => Real.log ((L : ℝ) + 2) / (L : ℝ)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun L : ℕ => ((L + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 (by norm_num)).comp hcast
  simpa only [Function.comp_def, pow_one, Nat.cast_add, Nat.cast_ofNat,
    one_mul, add_neg_cancel_right] using ht



end AbelianTargets

end

/-!
# Successive scale choice in Proposition 6.1

After the first scale is chosen, an arbitrary finite transverse bound
depending on that scale can be made small by a second scale. No uniform
bound in the first scale is assumed or needed.
-/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open Filter Topology

theorem solution (A : ℝ) (B : ℕ → ℝ)
    (L₀ M₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L M : ℕ, 1 ≤ L ∧ L₀ ≤ L ∧ 1 ≤ M ∧ M₀ ≤ M ∧
      A * Real.log ((L : ℝ) + 2) / (L : ℝ) + B L / (M : ℝ) < ε := by
  have htA : Tendsto (fun L : ℕ => A * Real.log ((L : ℝ) + 2) / (L : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using logarithmic_scale_error_tendsto.const_mul A
  have hε₂ : 0 < ε / 2 := half_pos hε
  have hfirst : ∀ᶠ L : ℕ in atTop,
      A * Real.log ((L : ℝ) + 2) / (L : ℝ) < ε / 2 :=
    htA.eventually (Iio_mem_nhds hε₂)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfirst
  let L := max N (max 1 L₀)
  have hLN : N ≤ L := le_max_left _ _
  have hL₁ : 1 ≤ L := (le_max_left 1 L₀).trans (le_max_right N (max 1 L₀))
  have hL₀ : L₀ ≤ L := (le_max_right 1 L₀).trans (le_max_right N (max 1 L₀))
  have htB : Tendsto (fun M : ℕ => B L / (M : ℝ)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have hsecond : ∀ᶠ M : ℕ in atTop, B L / (M : ℝ) < ε / 2 :=
    htB.eventually (Iio_mem_nhds hε₂)
  obtain ⟨P, hP⟩ := eventually_atTop.mp hsecond
  let M := max P (max 1 M₀)
  have hMP : P ≤ M := le_max_left _ _
  have hM₁ : 1 ≤ M := (le_max_left 1 M₀).trans (le_max_right P (max 1 M₀))
  have hM₀ : M₀ ≤ M := (le_max_right 1 M₀).trans (le_max_right P (max 1 M₀))
  refine ⟨L, M, hL₁, hL₀, hM₁, hM₀, ?_⟩
  have hsmall₁ := hN L hLN
  have hsmall₂ := hP M hMP
  linarith
