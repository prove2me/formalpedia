-- Prove2me | solution 1 for Zeta23.PrimeSide.GentryA_diag_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:35:09.881361+00:00
-- url     : https://prove2.me/submissions/1b0beb2a-a697-48c3-b10c-815d0702a1de

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
import Theorems.Thm_Zeta23_PrimeSide_P_part_integrable
import Theorems.Thm_Zeta23_PrimeSide_mu_part_integrable

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








lemma LocalHypsCore.phiHat_sq_mul_integrable_of_bdd (hF : LocalHypsCore cϱ p F) {g : ℝ → ℝ}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun r => F.phiHat r ^ 2 * g r) := by
  have := hF.phiHat_sq_integrable.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hc x))
  simpa only [mul_comm] using this














end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}











/-- Integrability of `φ̂(r)² Π_X(t+r)` (bounded × integrable). -/
lemma Pi_part_integrable (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd (hF.PiX_cont.comp (continuous_const_add t))
    (c := 3 * Real.sqrt p.X) (fun x => (hF.PiX_bound _).trans ?_)
  exact div_le_self (by positivity) (by linarith [abs_nonneg (t + x)])











end TraceAnalytic

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem solution (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (k : ℤ)
    (hk : 0 < p.tau k) :
    GentryA p F k k = (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by
  unfold GentryA
  have htrans : (∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau k) * Zeta23.nuX p.X τ)
      = ∫ r, F.phiHat r ^ 2 * Zeta23.nuX p.X (p.tau k + r) := by
    rw [← integral_add_right_eq_self _ (p.tau k)]
    congr 1; funext r; simp only [add_sub_cancel_right]; ring_nf
  rw [htrans]
  have hν : ∀ r, F.phiHat r ^ 2 * Zeta23.nuX p.X (p.tau k + r)
      = (F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r) + F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
        + F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) := by
    intro r; simp only [Zeta23.nuX]; ring
  simp_rw [hν]
  have h12 : Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r)
      + F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r)) :=
    (mu_part_integrable hΓ hF hk).add (Pi_part_integrable hF _)
  rw [integral_add h12 (P_part_integrable hF _),
    integral_add (mu_part_integrable hΓ hF hk) (Pi_part_integrable hF _)]
