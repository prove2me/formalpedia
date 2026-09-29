-- Prove2me | solution 1 for Zeta23.PrimeSide.sum_P_part_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:49:35.457554+00:00
-- url     : https://prove2.me/submissions/3c056805-ab56-4f13-a007-2dc8bc561cf9

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
import Theorems.Thm_Zeta23_PrimeSide_Aphi_mul_sum_cos_le
import Theorems.Thm_Zeta23_PrimeSide_P_part_eq

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

theorem solution (hF : LocalHypsCore cϱ p F) :
    |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2 * ∑ n ∈ primeRange p.X, acoef n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp_rw [P_part_eq hF]
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- now: |-2 * Σ_n Σ_k a_n A(y_n) cos(τ_k y_n)|
  rw [abs_mul, abs_neg, abs_two]
  have hterm : ∀ n ∈ primeRange p.X,
      |∑ k ∈ Finset.range p.d, acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)|
        ≤ acoef n * (p.L ^ 2 / (2 * Real.log 2)) := by
    intro n hn
    have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    have hfac : ∑ k ∈ Finset.range p.d, acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)
        = acoef n * (F.Aphi (ycoef n) * ∑ k ∈ Finset.range p.d, Real.cos (p.tau k * ycoef n)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfac, abs_mul, abs_of_nonneg ha]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · -- n = 1: a_1 = 0
      have hn1 : n = 1 := by
        have := (Finset.mem_Ioc.1 hn).1; omega
      subst hn1
      simp [acoef, ArithmeticFunction.vonMangoldt_apply_one]
    · gcongr
      apply Aphi_mul_sum_cos_le hF
      exact Real.log_le_log two_pos (by exact_mod_cast hn2)
  calc 2 * |∑ n ∈ primeRange p.X, ∑ k ∈ Finset.range p.d,
          acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)|
      ≤ 2 * ∑ n ∈ primeRange p.X,
          |∑ k ∈ Finset.range p.d, acoef n * F.Aphi (ycoef n) * Real.cos (p.tau k * ycoef n)| := by
        gcongr; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ n ∈ primeRange p.X, acoef n * (p.L ^ 2 / (2 * Real.log 2)) := by
        gcongr with n hn
        exact hterm n hn
    _ = p.L ^ 2 / Real.log 2 * ∑ n ∈ primeRange p.X, acoef n := by
        rw [← Finset.sum_mul]; field_simp
