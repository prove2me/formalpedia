-- Prove2me | solution 1 for Zeta23.WeilEF.logDeriv_GammaR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:21:28.895041+00:00
-- url     : https://prove2.me/submissions/8a585235-16d6-463f-a124-73217fd249ec

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series

-- from Zeta23.WeilEF.GammaRBracket
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/GammaRBracket.lean — the critical-line Γℝ bracket; proves
`Zeta23.WeilEF.gammaR_bracket`:

  logDeriv Γℝ(1/2+it) + logDeriv Γℝ(1/2−it) = Re ψ(1/4 + it/2) − log π      (t ∈ ℝ),

from Γℝ(s) = π^{−s/2}Γ(s/2) (Mathlib `Complex.Gammaℝ`), logDeriv Γℝ(s) = −(log π)/2 + ψ(s/2)/2
for re s > 0, and the conjugation symmetry ψ(conj z) = conj ψ(z) (from the partial-fraction
series Zeta23.DigammaSeries.hasSum_digamma_series).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex




end WeilEF
end Zeta23
end
open Zeta23
open Complex

theorem solution {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -((Real.log Real.pi : ℝ) : ℂ) / 2 + (1 / 2) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hGne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs2
  have hpow_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  -- Γℝ as a product of two functions
  have hfun : Complex.Gammaℝ = fun s => (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s
      * (Complex.Gamma ∘ fun s : ℂ => s / 2) s := by
    funext s; rw [Complex.Gammaℝ_def]; rfl
  -- derivative of the power factor
  have hdpow : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
    have h := ((hasDerivAt_id s).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (Or.inl hπ)
    convert h using 1
  have hdiff_pow : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    hdpow.differentiableAt
  have hΓdiff : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
    apply Complex.differentiableAt_Gamma
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hhalf : DifferentiableAt ℂ (fun s : ℂ => s / 2) s := differentiableAt_id.div_const 2
  have hdiff_G : DifferentiableAt ℂ (Complex.Gamma ∘ fun s : ℂ => s / 2) s := hΓdiff.comp s hhalf
  rw [hfun, logDeriv_mul s hpow_ne (by exact hGne) hdiff_pow hdiff_G,
    logDeriv_comp (g := fun s : ℂ => s / 2) (x := s) hΓdiff hhalf, ← Complex.digamma_def]
  -- the power factor's logDeriv
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = Complex.log Real.pi * (-1 / 2) := by
    rw [logDeriv_apply, hdpow.deriv]
    field_simp
  have h2 : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
    have : HasDerivAt (fun s : ℂ => s / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const 2
    exact this.deriv
  rw [h1, h2, (Complex.ofReal_log Real.pi_pos.le).symm]
  ring
