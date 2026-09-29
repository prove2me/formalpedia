-- Prove2me | solution 1 for Zeta23.PrimeSide.mu_abs_le_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:21:13.028259+00:00
-- url     : https://prove2.me/submissions/764529da-ae78-4f8c-a55e-a1636b79f3fd

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


/-- `l ≥ l₀` once `T ≥ 2π e^{l₀}`. -/
lemma Setting.le_l_of_T {p : Setting} {l₀ : ℝ} (hT : 2 * π * Real.exp l₀ ≤ p.T) : l₀ ≤ p.l := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  have h : Real.exp l₀ ≤ p.T / (2 * π) := by rw [le_div_iff₀ h2π]; linarith
  calc l₀ = Real.log (Real.exp l₀) := (Real.log_exp _).symm
    _ ≤ Real.log (p.T / (2 * π)) := Real.log_le_log (Real.exp_pos _) h
    _ = p.l := rfl

/-- `T ≥ 2π` (in particular `T ≥ 1`, `T > 0`) once `T ≥ 2π e^{l₀}` with `l₀ ≥ 0`. -/
lemma Setting.twopi_le_T {p : Setting} {l₀ : ℝ} (hl₀ : 0 ≤ l₀) (hT : 2 * π * Real.exp l₀ ≤ p.T) :
    2 * π ≤ p.T := by
  have : (1:ℝ) ≤ Real.exp l₀ := Real.one_le_exp hl₀
  nlinarith [Real.pi_pos]









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

theorem solution (hΓ : Zeta23.GammaFacts) : ∃ T₀ : ℝ, ∀ p : Setting, T₀ ≤ p.T →
    ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  refine ⟨2 * π * Real.exp (2 * |C| + 1), fun p hT τ hτ => ?_⟩
  have hl : 2 * |C| + 1 ≤ p.l := Setting.le_l_of_T hT
  have h2π : 2 * π ≤ p.T := Setting.twopi_le_T (by positivity) hT
  have hT1 : 1 ≤ p.T := by linarith [Real.pi_gt_three]
  have hτpos : 0 < τ := by linarith [hτ.1]
  have hτ1 : 1 ≤ |τ| := by rw [abs_of_pos hτpos]; linarith [hτ.1]
  have hst := hC τ hτ1
  rw [abs_of_pos hτpos] at hst
  have hCτ : C / τ ^ 2 ≤ |C| := by
    calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ |C| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          have : 1 ≤ τ := by linarith [hτ.1]
          nlinarith
      _ = |C| := div_one _
  -- log(τ/2π) ≤ log(2T/2π) = l + log 2
  have hlog : Real.log (τ / (2 * π)) ≤ p.l + Real.log 2 := by
    have : Real.log (τ / (2 * π)) ≤ Real.log (2 * p.T / (2 * π)) :=
      Real.log_le_log (by positivity) (by gcongr; exact hτ.2)
    refine this.trans (le_of_eq ?_)
    rw [show 2 * p.T / (2 * π) = 2 * (p.T / (2 * π)) by ring,
      Real.log_mul (by norm_num) (by positivity)]
    simp [Setting.l, Zeta23.l, add_comm]
  have hup : Zeta23.mu τ ≤ p.l := by
    have h1 : Zeta23.mu τ ≤ 1 / (2 * π) * Real.log (τ / (2 * π)) + |C| := by
      linarith [(abs_le.1 hst).2]
    have h2 : 1 / (2 * π) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left zero_le_one (by norm_num); linarith [Real.pi_gt_three]
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (zero_lt_two' ℝ); linarith
    have h0 : 0 ≤ p.l + Real.log 2 := by
      linarith [abs_nonneg C, Real.log_nonneg (one_le_two : (1:ℝ) ≤ 2)]
    calc Zeta23.mu τ ≤ 1 / (2 * π) * (p.l + Real.log 2) + |C| := by
          have : 1 / (2 * π) * Real.log (τ / (2 * π)) ≤ 1 / (2 * π) * (p.l + Real.log 2) := by
            gcongr
          linarith
      _ ≤ 1 / 2 * (p.l + Real.log 2) + |C| := by gcongr
      _ ≤ p.l := by linarith
  have hlo : -p.l ≤ Zeta23.mu τ := by
    have := hΓ.mu_zero_le τ; have := hΓ.neg_one_lt_mu_zero
    linarith [abs_nonneg C]
  exact abs_le.2 ⟨hlo, hup⟩
