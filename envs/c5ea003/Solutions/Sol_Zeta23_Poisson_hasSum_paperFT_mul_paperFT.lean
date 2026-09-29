-- Prove2me | solution 1 for Zeta23.Poisson.hasSum_paperFT_mul_paperFT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:44:45.19594+00:00
-- url     : https://prove2.me/submissions/2ed9e8ff-9b3e-4a06-b25c-d5d49ba35c57

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_Poisson_Gaux_continuous
import Theorems.Thm_Zeta23_Poisson_fourier_Gaux
import Theorems.Thm_Zeta23_Poisson_gInt_eq_zero_of_not_mem
import Theorems.Thm_Zeta23_Poisson_isBigO_of_decay

-- from Zeta23.Poisson.PaperFT
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/

theorem paperFT_def (f : ℝ → ℂ) (z : ℂ) : paperFT f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl

/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/

theorem integral_const_mul_C (r : ℂ) (f : ℝ → ℂ) : (∫ a, r * f a) = r * ∫ a, f a :=
  integral_const_mul r f




/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/










end Zeta23
end

-- from Zeta23.Poisson
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
[lem:poisson] "Poisson summation for the Gabor system", the paper §2.2:

  "For all τ, τ' ∈ ℝ,
     K_∞(τ,τ') := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L·Φ(τ−τ'),   in particular   Σ_{k∈ℤ} φ̂(τ−τ_k)² = aL²."

Here τ_k := T + k h, h := 2π/L [eq:fk], Φ := (φ²)^ [eq:PhigA], a := L⁻¹∫φ² [eq:abdef], and
φ̂(s) = ∫ φ(u) e^{isu} du is the paper's Fourier convention (`Zeta23.paperFT`).  Only the
real-argument identity is proved (that is all [prop:block](ii) uses; the complex continuation
mentioned in [rem:pairblock] is not used by the proof).

Proof route (the paper's, rearranged so that Fourier inversion is not needed): with
  G(ξ) := L · ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du      (= L e^{−iTLξ}(φ_τ ∗ φ_{τ'})(Lξ)),
G is continuous with support in [−1,1] and G(k) = 0 for k ∈ ℤ∖{0} (because φ(u) = 0 for
|u| ≥ L/2), G(0) = L ∫ φ(u)φ(−u)e^{i(τ−τ')u} du = L Φ(τ−τ') (φ even), and a Fubini computation
gives 𝓕G(w) = φ̂(τ−τ_w) φ̂(τ'−τ_w) for Mathlib's 𝓕 and every real w (τ_w := T + w·2π/L).
Mathlib's Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
(Σ_k G(k) = Σ_n 𝓕G(n)) then gives the claim; summability of n ↦ φ̂(τ−τ_n)φ̂(τ'−τ_n) comes from
the decay |φ̂(r)| ≪ (1+r²)⁻¹, i.e. [eq:hfbound]/[eq:psidef].
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23

namespace Poisson

/-! #### A decay-to-`IsBigO` lemma -/


/-! #### The auxiliary function `G` -/

variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)



variable {φ L T τ τ'}






/-- `G(ξ) = 0` for `|ξ| ≥ 1`. -/
theorem Gaux_eq_zero (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {ξ : ℝ}
    (hξ : 1 ≤ |ξ|) : Gaux φ L T τ τ' ξ = 0 := by
  unfold Gaux
  rw [← integral_zero]
  congr 1 with u
  apply gInt_eq_zero_of_not_mem hL hsupp
  rintro ⟨h1, -⟩
  linarith

/-- `G(0) = L · (φ²)^(τ − τ')` (uses φ even). -/
theorem Gaux_zero (heven : ∀ u, φ (-u) = φ u) :
    Gaux φ L T τ τ' 0 = L * paperFT (fun u => ((φ u ^ 2 : ℝ) : ℂ)) ((τ - τ' : ℝ) : ℂ) := by
  unfold Gaux gInt
  rw [paperFT_def, integral_const_mul_C]
  congr 1
  congr 1 with u
  simp only [mul_zero, zero_sub, heven]
  push_cast
  ring_nf



/-! #### The abstract identity -/


end Poisson

namespace Taper

variable {ϱ : ℝ → ℝ} {L w : ℝ}




end Taper

namespace Params

variable {P : Params} {T : ℝ}


variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL




end Params

end Zeta23
open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Poisson
variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)
variable {φ L T τ τ'}

theorem solution {φ : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) (heven : ∀ u, φ (-u) = φ u)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
                        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ))
      (L * paperFT (fun u => ((φ u ^ 2 : ℝ) : ℂ)) ((τ - τ' : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hdecay
  set G := Gaux φ L T τ τ' with hG
  have hGc : Continuous G := Gaux_continuous hL hφc hsupp
  -- G has compact support, hence is O(|x|^{-2})
  have hGO : G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    refine IsBigO.of_bound 0 ?_
    have hev : ∀ᶠ x : ℝ in cocompact ℝ, (1 : ℝ) ≤ ‖x‖ :=
      tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with x hx
    rw [hG, Gaux_eq_zero hL hsupp (by simpa using hx)]
    simp
  -- decay of 𝓕 G
  have hφhat_bdd : ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ ≤ C := by
    intro s
    have := hC s
    have h1 : ‖paperFT (fun u => (φ u : ℂ)) s‖ * 1 ≤ ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) := by
      gcongr; nlinarith
    linarith
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hφhat_bdd 0)
  have hFO : 𝓕 G =O[cocompact ℝ] fun x : ℝ => |x| ^ (-2 : ℝ) := by
    apply isBigO_of_decay (c := τ - T) (h := 2 * π / L) (C := C * C) (by positivity)
    intro w
    rw [hG, fourier_Gaux hL hφc hsupp w, norm_mul]
    have e1 : τ - T - w * (2 * π / L) = τ - (T + w * (2 * π / L)) := by ring
    rw [e1]
    calc ‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
          * ‖paperFT (fun u => (φ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖
          * (1 + (τ - (T + w * (2 * π / L))) ^ 2)
        = (‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
            * (1 + (τ - (T + w * (2 * π / L))) ^ 2))
          * ‖paperFT (fun u => (φ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖ := by ring
      _ ≤ C * C := by
        apply mul_le_mul (hC _) (hφhat_bdd _) (norm_nonneg _) hC0
  have hsum : Summable fun n : ℤ => 𝓕 G n :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hFO.comp_tendsto Int.tendsto_coe_cofinite)
  -- Poisson summation at x = 0
  have key := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hGc one_lt_two hGO hsum 0
  have lhs : ∑' n : ℤ, G (0 + n) = G 0 := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      rw [zero_add, hG, Gaux_eq_zero hL hsupp]
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hn
  have rhs : ∑' n : ℤ, 𝓕 G n * fourier n ((0 : ℝ) : UnitAddCircle) = ∑' n : ℤ, 𝓕 G n := by
    congr 1 with n
    rw [fourier_coe_apply]
    simp
  rw [lhs, rhs] at key
  -- conclude
  have hs : HasSum (fun n : ℤ => 𝓕 G n) (G 0) := by
    rw [key]; exact hsum.hasSum
  rw [hG, Gaux_zero heven] at hs
  convert hs using 1
  funext k
  rw [fourier_Gaux hL hφc hsupp]
