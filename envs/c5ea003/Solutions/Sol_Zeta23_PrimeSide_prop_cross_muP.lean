-- Prove2me | solution 1 for Zeta23.PrimeSide.prop_cross_muP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:19:02.651051+00:00
-- url     : https://prove2.me/submissions/c15d57ad-f23d-4d7e-bc0e-00a09fa9fe8e

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
import Theorems.Thm_Zeta23_PrimeSide_Mform_mu_PX_eq
import Theorems.Thm_Zeta23_PrimeSide_abs_Mform_cos_phase_le
import Theorems.Thm_Zeta23_PrimeSide_mu_abs_le_l

-- from Zeta23.PrimeSideA.Basic
section
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

lemma Setting.one_le_T {p : Setting} {l₀ : ℝ} (hl₀ : 0 ≤ l₀) (hT : 2 * π * Real.exp l₀ ≤ p.T) :
    1 ≤ p.T := by
  have := Setting.twopi_le_T hl₀ hT; linarith [Real.pi_gt_three]

/-- `X ≥ x₀` once `T ≥ 2π exp(|x₀|/λ)` (`X = (T/2π)^λ → ∞`; this is the "T ≥ T₀(λ)" of §5). -/
lemma Setting.le_X_of_T {p : Setting} (hlam : 0 < p.lam) {x₀ : ℝ}
    (hT : 2 * π * Real.exp (|x₀| / p.lam) ≤ p.T) : x₀ ≤ p.X := by
  have hl : |x₀| / p.lam ≤ p.l := Setting.le_l_of_T hT
  have h1 : |x₀| ≤ p.lam * p.l := by rwa [div_le_iff₀' hlam] at hl
  calc x₀ ≤ |x₀| := le_abs_self _
    _ ≤ p.lam * p.l := h1
    _ ≤ Real.exp (p.lam * p.l) := by linarith [Real.add_one_le_exp (p.lam * p.l)]
    _ = p.X := rfl







/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/






/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/

lemma LocalHypsCore.eight_le_L (hF : LocalHypsCore cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHypsCore.L_pos (hF : LocalHypsCore cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]



lemma LocalHypsCore.integral_Phi_sq_le (hF : LocalHypsCore cϱ p F) :
    ∫ x, F.Phi x ^ 2 ≤ 2 * π * p.L := by
  rw [hF.Phi_sq_integral]
  have hb1 : F.b ≤ 1 := hF.b_le_a.trans hF.a_le_one
  have hL := hF.L_pos
  calc 2 * π * F.b * p.L = (2 * π * p.L) * F.b := by ring
    _ ≤ (2 * π * p.L) * 1 := by gcongr
    _ = 2 * π * p.L := mul_one _

















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
end

-- from Zeta23.PrimeSideA.CrossMuPCore
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# Analytic core of [prop:cross] (i): the double integration by parts for `𝓜[u, cos(·y)]`

See `Zeta23/PrimeSideA/CrossMuP.lean` for the statement of [prop:cross](i) and the paper text.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

section CrossMuPCore
variable {Φ : ℝ → ℝ} {T : ℝ}









/-- **The oscillatory bound** (§5.4: "`|∫_I m(τ′)cos(τ′y)dτ′| ≤ (2 sup|m| + ∫_I|m′|)/y`"), here in
the explicit form: if `Φ, u ∈ C¹`, `|u| ≤ B` and `|u′| ≤ D` on `I = [T,2T]`, `T ≥ 0`, `y ≠ 0`, then
`|𝓜[u, cos(·y)]| ≤ (4B + D·T)·(∫_ℝ Φ²)/|y|` — the case `θ = 0` of `abs_Mform_cos_phase_le`. -/
theorem abs_Mform_cos_le (hT : 0 ≤ T) (hΦ : ContDiff ℝ 1 Φ)
    (hΦint : Integrable (fun x => Φ x ^ 2)) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {B D : ℝ}
    (hB : ∀ τ ∈ Icc T (2 * T), |u τ| ≤ B) (hD : ∀ τ ∈ Icc T (2 * T), |deriv u τ| ≤ D)
    {y : ℝ} (hy : y ≠ 0) :
    |Mform Φ T u (fun t => Real.cos (t * y))| ≤ (4 * B + D * T) * (∫ x, Φ x ^ 2) / |y| := by
  simpa only [add_zero] using abs_Mform_cos_phase_le hT hΦ hΦint hu hB hD hy 0

end CrossMuPCore

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.CrossMuP
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
Imported by PrimeSideA.lean.
-/

/-!
# [prop:cross] (i):  `𝓜[μ, P_X] ≪ l √X`   (the paper §5.4)

Paper proof (§5.4): with `m(τ′) := ∫_I Φ(τ−τ′)² μ(τ) dτ`, "`m` is `C¹`, and differentiating
under the integral and integrating by parts in `τ`,
`m′(τ′) = μ(T)Φ(T−τ′)² − μ(2T)Φ(2T−τ′)² + ∫_I μ′(τ)Φ(τ−τ′)² dτ`, so that `∫_I|m′| ≪ lL`.
For `y ≥ log 2`, integrating by parts, `|∫_I m(τ′)cos(τ′y)dτ′| ≤ (2 sup|m| + ∫_I|m′|)/y ≪ lL/y`.
Therefore `|𝓜[μ,P_X]| = |π⁻¹ Σ_n a_n ∫_I m(τ′)cos(τ′y_n)dτ′| ≪ lL Σ_{n≤X} a_n/log n ≪ lL √X/L = l√X`
by (eq:cheb1)."

Formal route (same two integrations by parts, but ordered so that NO differentiation under the
integral sign is needed): Fubini with `τ` outer; IBP in `τ′` on `Φ(τ−τ′)²·cos(τ′y)` (the derivative
lands on `Φ²`, `Φ ∈ C¹`); Fubini swap; IBP in `τ` on `μ(τ)·(Φ²)′(τ−τ′)` (the derivative lands on
`μ`); then the sup bounds `|μ| ≤ l`, `|μ′| ≤ C/T` on `I` and `∫_S Φ(·−c)² ≤ ∫_ℝ Φ² = 2πbL` give
`|𝓜[μ, cos(·y)]| ≤ (4l + C)·2πbL/|y|`, and [eq:cheb1] (`cheb1c`: `Σ Λ(n)/(√n log n) ≪ √X/log X`, `log X = L`)
finishes.  Inputs: `LocalHyps` (Φ ∈ C¹, Φ even, ∫Φ² = 2πbL, b ≤ a ≤ 1, l ≥ 1), H-Γ (`smooth`,
`deriv_bound`, via `mu_abs_le_l`), H-cheb (`cheb1c`).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide


/-! ## [prop:cross] (i) -/

section CrossMuP
variable (cϱ lam : ℝ)



end CrossMuP

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem solution (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)| ≤ C * (p.l * Real.sqrt p.X)) := by
  obtain ⟨T₁, hT₁⟩ := mu_abs_le_l hΓ
  obtain ⟨Cd, hCd⟩ := hΓ.deriv_bound
  obtain ⟨Cc, hCc⟩ := hcheb.cheb1c
  have hμ : ContDiff ℝ 1 Zeta23.mu := hΓ.smooth.of_le (by exact_mod_cast le_top)
  refine ⟨2 * (4 + |Cd|) * |Cc|, max T₁ (2 * π * Real.exp (|(2:ℝ)| / lam)), ?_⟩
  intro p F hplam hT hF
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hT
  have hT2 : 2 * π * Real.exp (|(2:ℝ)| / p.lam) ≤ p.T := by rw [hplam]; exact (le_max_right _ _).trans hT
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hT1 : 1 ≤ p.T := Setting.one_le_T (div_nonneg (abs_nonneg _) hlam0.le) hT2
  have hT0 : 0 ≤ p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hL := hF.L_pos
  have hX2 : 2 ≤ p.X := Setting.le_X_of_T hlam0 hT2
  have hlogX : Real.log p.X = p.L := by simp [Setting.X]
  -- sup bounds for μ, μ' on I
  have hB : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l := hT₁ p hT₁'
  have hD : ∀ τ ∈ Icc p.T (2 * p.T), |deriv Zeta23.mu τ| ≤ |Cd| / p.T := by
    intro τ hτ
    have hτ1 : 1 ≤ |τ| := by rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.1]
    refine (hCd τ hτ1).trans ?_
    rw [abs_of_nonneg (by linarith [hτ.1])]
    calc Cd / τ ≤ |Cd| / τ := div_le_div_of_nonneg_right (le_abs_self _) (by linarith [hτ.1])
      _ ≤ |Cd| / p.T := div_le_div_of_nonneg_left (abs_nonneg _) (by linarith) hτ.1
  -- the oscillatory bound at each frequency y_n, n ≥ 2
  set S : ℝ := ∫ x, F.Phi x ^ 2 with hSdef
  have hS : S ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  set K : ℝ := (4 * p.l + |Cd| / p.T * p.T) * S with hKdef
  have hKeq : K = (4 * p.l + |Cd|) * S := by
    have hTne : p.T ≠ 0 := by linarith
    rw [hKdef, div_mul_cancel₀ _ hTne]
  have hK0 : 0 ≤ K := by rw [hKeq]; positivity
  have hosc : ∀ n ∈ primeRange p.X,
      |(-(1 / Real.pi) * acoef n) * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * ycoef n))|
        ≤ (1 / Real.pi) * K * (acoef n / ycoef n) := by
    intro n hn
    have ha0 : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · -- n = 1: a_1 = 0
      have hn1 : n = 1 := by
        have : 0 < n := (Finset.mem_Ioc.mp hn).1
        omega
      subst hn1
      simp [acoef]
    · have hy : 0 < ycoef n := Real.log_pos (by exact_mod_cast h2)
      have hM := abs_Mform_cos_le hT0 hF.Phi_contDiff hF.Phi_sq_integrable hμ hB hD hy.ne'
      rw [abs_of_pos hy] at hM
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi),
        abs_of_nonneg ha0]
      calc 1 / Real.pi * acoef n * |Mform F.Phi p.T Zeta23.mu fun t => Real.cos (t * ycoef n)|
          ≤ 1 / Real.pi * acoef n * (K / ycoef n) := by gcongr
        _ = 1 / Real.pi * K * (acoef n / ycoef n) := by ring
  -- sum over n
  rw [Mform_mu_PX_eq hF.Phi_contDiff.continuous hμ.continuous]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hosc).trans ?_)
  rw [← Finset.mul_sum]
  -- Σ a_n / y_n ≤ Cc √X / log X = Cc √X / L
  have hsum : ∑ n ∈ primeRange p.X, acoef n / ycoef n ≤ |Cc| * Real.sqrt p.X / p.L := by
    have h := hCc p.X hX2
    rw [hlogX] at h
    have e : ∑ n ∈ primeRange p.X, acoef n / ycoef n
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) / (Real.sqrt n * Real.log n) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [acoef, ycoef, div_div]
    rw [e]
    refine h.trans ?_
    gcongr; exact le_abs_self _
  have hsum0 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n / ycoef n :=
    Finset.sum_nonneg fun n _ => div_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (Real.log_natCast_nonneg _)
  calc 1 / Real.pi * K * ∑ n ∈ primeRange p.X, acoef n / ycoef n
      ≤ 1 / Real.pi * ((4 * p.l + |Cd|) * (2 * π * p.L)) * (|Cc| * Real.sqrt p.X / p.L) := by
        rw [hKeq]; gcongr
    _ = 2 * (4 * p.l + |Cd|) * |Cc| * Real.sqrt p.X := by field_simp
    _ ≤ 2 * ((4 + |Cd|) * p.l) * |Cc| * Real.sqrt p.X := by
        gcongr
        nlinarith [abs_nonneg Cd]
    _ = 2 * (4 + |Cd|) * |Cc| * (p.l * Real.sqrt p.X) := by ring
