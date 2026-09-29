-- Prove2me | solution 1 for Zeta23.MuFields.re_digamma_vertical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:12:16.45901+00:00
-- url     : https://prove2.me/submissions/4e11d3dd-6f98-4bd5-b4cf-3eceed479b6e

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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series
import Theorems.Thm_Zeta23_DigammaSeries_summable_digamma_series
import Theorems.Thm_Zeta23_MuFields_re_term_eq

-- from Zeta23.GammaFacts.Series
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Series.lean — the digamma partial-fraction series.

Target:  digamma z = −γ − 1/z + ∑'_{n≥0} (1/(n+1) − 1/(z+n+1))   for z ∈ ℂ_ℤ,
the Mathlib-missing piece needed for the remaining H-Γ fields
([eq:mufacts]; see Zeta23/GammaFacts.lean).  Route (modelled on Mathlib's
Analysis/SpecialFunctions/Trigonometric/Cotangent.lean, which does the same for
sin → cot):
  1. Weierstrass factors  1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}, with
     ‖wTerm n z‖ ≤ 3(‖z‖/(n+1))² for n+1 ≥ ‖z‖  (M-test input);
  2. the finite identity  (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1+wTerm n z);
  3. N → ∞ (GammaSeq_tendsto_Gamma + tendsto_harmonic_sub_log):
       Γ(z)⁻¹ = z·e^{γz}·∏'_n (1 + wTerm n z)            [Weierstrass product]
  4. logDeriv via Complex.logDeriv_tprod_eq_tsum          [digamma series].
This file has steps 1–3; step 4 is `digamma_series` at the bottom.
-/

noncomputable section

namespace Zeta23
namespace DigammaSeries

open Complex Filter Topology








/-! ### The finite identity and the Weierstrass product -/







/-- **The digamma partial-fraction series** (paper [eq:mufacts]'s parenthetical, the
keystone for the remaining H-Γ fields):
ψ(z) = −γ − 1/z + Σ'ₙ (1/(n+1) − 1/(z+n+1)) for z off the integers. -/
theorem digamma_series {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma z = -(Real.eulerMascheroniConstant : ℂ) - 1 / z
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / (z + n + 1)) := by
  rw [(hasSum_digamma_series hz).tsum_eq]
  ring

end DigammaSeries
end Zeta23
end
end

-- from Zeta23.GammaFacts.Mu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Mu.lean — the remaining H-Γ fields from the digamma series.  Canonical text: the paper [eq:mufacts]:
"μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1, μ(τ) = (1/2π)log(|τ|/2π)
+ O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus the [eq:muints] integrals.
The ψ-toolkit is developed at a parametrized abscissa
a ∈ (0,1) (covers ζ's a = 1/4 and, composed with the recurrence, Theorem E's
a = 1/4 + κ/2).  Foundation: Zeta23.DigammaSeries.
-/

noncomputable section

namespace Zeta23
namespace MuFields

open Complex Filter Topology

variable {a : ℝ}

/-- Points a + it with a ∈ (0,1) avoid the integers. -/
lemma abscissa_mem (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; exact ha1
    exact_mod_cast h
  omega


/-- Re(1/z) on the line. -/
lemma re_inv_eq (t : ℝ) :
    ((1 : ℂ) / ((a : ℂ) + Complex.I * t)).re = a / (a ^ 2 + t ^ 2) := by
  rw [one_div, Complex.inv_re]
  have hre : ((a : ℂ) + Complex.I * t).re = a := by simp
  have him : ((a : ℂ) + Complex.I * t).im = t := by simp
  rw [hre, Complex.normSq_apply, hre, him]
  ring



/-! ### Monotonicity on the vertical line, and the μ order facts -/






/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
open Zeta23
open MuFields
open Complex Filter Topology
variable {a : ℝ}

theorem solution (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re
      = -Real.eulerMascheroniConstant - a / (a ^ 2 + t ^ 2)
        + ∑' n : ℕ,
          (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hmem := abscissa_mem ha0 ha1 t
  have h := Zeta23.DigammaSeries.digamma_series hmem
  have hre := congrArg Complex.re h
  rw [hre]
  rw [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.ofReal_re]
  congr 1
  · congr 1
    exact re_inv_eq t
  · -- re of the tsum = tsum of re
    have hs := Zeta23.DigammaSeries.summable_digamma_series hmem
    have hmap := Complex.reCLM.map_tsum hs
    rw [show (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))).re
      = Complex.reCLM (∑' n : ℕ, ((1 : ℂ) / ((n : ℂ) + 1)
        - 1 / (((a : ℂ) + Complex.I * t) + n + 1))) from rfl, hmap]
    congr 1
    funext n
    exact re_term_eq t n
