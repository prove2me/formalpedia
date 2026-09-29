-- Prove2me | solution 1 for Zeta23.PrimeSide.mu_part_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:53:44.40651+00:00
-- url     : https://prove2.me/submissions/4dedd7bb-5b3c-4a10-aefb-dbd2a32d30c0

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Theorems.Thm_Zeta23_PrimeSide_mu_linear_bound

-- from Zeta23.PrimeSideA.Basic
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/


-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/




/-! ### Bilinearity and symmetry of 𝓜[·,·] (§5.4: "a symmetric bilinear form (Φ² is even)") -/

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}








end MformLemmas


/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/

section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}



end SupBound


/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}












/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/






/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/






















end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}






















end TraceAnalytic

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem solution (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {K : ℝ}
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (t + r)) - 2 * π * F.a * p.L * Zeta23.mu t|
      ≤ (K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by
  have ht0 : 0 < t := by linarith
  obtain ⟨M, hM0, hM⟩ := mu_linear_bound hΓ
  have hmeas : AEStronglyMeasurable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) volume := by
    have hc : Continuous fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r) := by
      have := hΓ.smooth.continuous; have := hF.phiHat_cont; fun_prop
    exact hc.aestronglyMeasurable
  have hint : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) := by
    refine Integrable.mono'
      ((hF.phiHat_sq_integrable.const_mul (M + t)).add hF.phiHat_sq_mul_abs_integrable) hmeas ?_
    refine Filter.Eventually.of_forall fun r => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have htr : |t + r| ≤ t + |r| := by
      calc |t + r| ≤ |t| + |r| := abs_add_le _ _
        _ = t + |r| := by rw [abs_of_pos ht0]
    calc F.phiHat r ^ 2 * |Zeta23.mu (t + r)| ≤ F.phiHat r ^ 2 * (M + |t + r|) := by
          gcongr; exact hM _
      _ ≤ F.phiHat r ^ 2 * (M + (t + |r|)) := by gcongr
      _ = (M + t) * F.phiHat r ^ 2 + F.phiHat r ^ 2 * |r| := by ring
  have hconst : 2 * π * F.a * p.L * Zeta23.mu t = ∫ r, F.phiHat r ^ 2 * Zeta23.mu t := by
    rw [integral_mul_const, hF.phiHat_sq_integral]
  rw [hconst, ← integral_sub hint (hF.phiHat_sq_integrable.mul_const _)]
  have hgi : Integrable (fun r => (K * (F.phiHat r ^ 2 * |r|) + 10 * (F.phiHat r ^ 2 * r ^ 2)) / t) :=
    ((hF.phiHat_sq_mul_abs_integrable.const_mul K).add
      (hF.phiHat_sq_mul_sq_integrable.const_mul 10)).div_const t
  rw [← Real.norm_eq_abs]
  calc ‖∫ r, F.phiHat r ^ 2 * Zeta23.mu (t + r) - F.phiHat r ^ 2 * Zeta23.mu t‖
      ≤ ∫ r, (K * (F.phiHat r ^ 2 * |r|) + 10 * (F.phiHat r ^ 2 * r ^ 2)) / t := by
        refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun r => ?_)
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc F.phiHat r ^ 2 * |Zeta23.mu (t + r) - Zeta23.mu t|
            ≤ F.phiHat r ^ 2 * ((K * |r| + 10 * r ^ 2) / t) := by gcongr; exact hK t ht r
          _ = _ := by ring
    _ = (K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by
        rw [integral_div, integral_add (hF.phiHat_sq_mul_abs_integrable.const_mul K)
          (hF.phiHat_sq_mul_sq_integrable.const_mul 10), integral_const_mul, integral_const_mul]
