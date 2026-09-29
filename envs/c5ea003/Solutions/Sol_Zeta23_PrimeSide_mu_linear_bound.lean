-- Prove2me | solution 1 for Zeta23.PrimeSide.mu_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:38:14.082865+00:00
-- url     : https://prove2.me/submissions/661852af-feba-45d7-9677-4492e3478ec0

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

theorem solution (hΓ : Zeta23.GammaFacts) : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, |Zeta23.mu τ| ≤ M + |τ| := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓ.smooth.continuous.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  refine ⟨max M₁ (1 + |C|), le_max_of_le_right (by positivity), fun τ => ?_⟩
  rcases le_or_gt 1 |τ| with h1 | h1
  · -- |τ| ≥ 1: Stirling
    have hst := hC τ h1
    have hx : 0 < |τ| / (2 * π) := by positivity
    have hlog : |Real.log (|τ| / (2 * π))| ≤ |τ| / (2 * π) + 2 * π := by
      rw [abs_le]; constructor
      · have := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
        rw [Real.log_inv] at this
        have : (|τ| / (2 * π))⁻¹ ≤ 2 * π := by
          rw [inv_div, div_le_iff₀ (by linarith : (0:ℝ) < |τ|)]; nlinarith [Real.pi_pos]
        linarith
      · linarith [Real.log_le_sub_one_of_pos hx, Real.pi_pos]
    have hCτ : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self _
        _ ≤ |C| / 1 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos; nlinarith [sq_abs τ]
        _ = |C| := div_one _
    have h2 : |1 / (2 * π) * Real.log (|τ| / (2 * π))| ≤ 1 + |τ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
      calc 1 / (2 * π) * |Real.log (|τ| / (2 * π))| ≤ 1 / (2 * π) * (|τ| / (2 * π) + 2 * π) := by
            gcongr
        _ = |τ| / (2 * π) ^ 2 + 1 := by field_simp
        _ ≤ |τ| / 1 + 1 := by
            gcongr; nlinarith [Real.pi_gt_three]
        _ = 1 + |τ| := by ring
    calc |Zeta23.mu τ| = |(Zeta23.mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π)))
          + 1 / (2 * π) * Real.log (|τ| / (2 * π))| := by ring_nf
      _ ≤ |Zeta23.mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π))|
          + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := abs_add_le _ _
      _ ≤ |C| + (1 + |τ|) := add_le_add (hst.trans hCτ) h2
      _ ≤ max M₁ (1 + |C|) + |τ| := by linarith [le_max_right M₁ (1 + |C|)]
  · have := hM₁ τ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    simp only [Real.norm_eq_abs] at this
    linarith [le_max_left M₁ (1 + |C|), abs_nonneg τ]
