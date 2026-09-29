-- Prove2me | solution 1 for Zeta23.StirlingVert.re_digamma_stirling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:14:31.273381+00:00
-- url     : https://prove2.me/submissions/5e6237ba-682b-441a-849a-27f261a1225a

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Theorems.Thm_Zeta23_StirlingVert_digamma_stirling

-- from Zeta23.GammaFacts.StirlingVert
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/StirlingVert.lean — Stirling for the digamma function on vertical lines.  Target: the H-Γ field `GammaFacts.stirling`
  "μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²)  (|τ| ≥ 1)"   [eq:mufacts]
via the COMPLEX asymptotic  ψ(w) = log w − 1/(2w) + O(1/(Im w)²)  for 0 < Re w ≤ 1,
|Im w| ≥ 1, proved from the partial-fraction series (Zeta23.DigammaSeries)
WITHOUT Euler–Maclaurin:  on each unit interval
   1/(x+w) = 1/(m+w) − (x−m)/(m+w)² + (x−m)²/((m+w)²(x+w))        (exact algebra),
so ∫_m^{m+1} dx/(x+w) = 1/(m+w) − 1/(2(m+w)²) + ε_m, |ε_m| ≤ 1/(3|m+w|²|Im w|), while the
left side is log(m+1+w) − log(m+w) (FTC for Complex.log on the slit plane) and telescopes.
-/

noncomputable section

namespace Zeta23
namespace StirlingVert

open Complex Filter Topology MeasureTheory intervalIntegral Set

/-! ### ℂ-specialized interval-integral constant rules (the RCLike-generic Mathlib versions do
not match ℂ's default instance path under `rw`; cf. Zeta23.integral_const_mul_C) -/



/-! ### Elementary bounds for points in the right half-plane -/





/-! ### The antiderivative `F(x) = log(x + w)` on `[0, ∞)` -/



/-! ### The per-interval expansion -/





/-! ### The sequence `z_n := n + 1 + w` -/

section Seq
variable {w : ℂ}












/-! ### Bounds: `Σ_{n<N} 1/‖z_n‖² ≤ 2/|im w|` by a real telescoping -/




/-! ### Summability of the remainders and tsum bounds -/









/-! ### Limits -/



/-! ### The exact identity and the Stirling bound -/





end Seq

/-! ### Real part on vertical lines, and the H-Γ field for μ -/

section RePart




end RePart

end StirlingVert
end Zeta23
end
open Zeta23
open StirlingVert
open Complex Filter Topology MeasureTheory intervalIntegral Set

theorem solution {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
      ≤ 4 / t ^ 2 := by
  set w : ℂ := (a : ℂ) + Complex.I * t with hwdef
  have hre : w.re = a := by simp [hwdef]
  have him : w.im = t := by simp [hwdef]
  have hw : 0 < w.re := by rw [hre]; exact ha0
  have ht' : 1 / 2 ≤ |w.im| := by rw [him]; exact ht
  have hmain := digamma_stirling hw ht'
  rw [him] at hmain
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  -- real parts
  have hlogre : (Complex.log w).re = (1 / 2) * Real.log (a ^ 2 + t ^ 2) := by
    rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt (by positivity)]
    ring
  have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring, Complex.re_ofReal_mul,
      Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hdiff : (Complex.digamma w).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)
      = (Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re - a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [Complex.add_re, Complex.sub_re, hlogre, hinvre]; ring
  rw [hdiff]
  have h1 : |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| ≤ 3 / t ^ 2 :=
    le_trans (Complex.abs_re_le_norm _) hmain
  have h2 : |a / (2 * (a ^ 2 + t ^ 2))| ≤ 1 / t ^ 2 := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) ht2]
    nlinarith
  calc |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re - a / (2 * (a ^ 2 + t ^ 2))|
      ≤ |(Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w).re| + |a / (2 * (a ^ 2 + t ^ 2))| :=
        abs_sub _ _
    _ ≤ 3 / t ^ 2 + 1 / t ^ 2 := add_le_add h1 h2
    _ = 4 / t ^ 2 := by ring
