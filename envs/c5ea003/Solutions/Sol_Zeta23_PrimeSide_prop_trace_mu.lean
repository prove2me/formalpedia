-- Prove2me | solution 1 for Zeta23.PrimeSide.prop_trace_mu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:41:50.713635+00:00
-- url     : https://prove2.me/submissions/c317b342-234d-4424-8a14-efcbf18f0750

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Theorems.Thm_Zeta23_PrimeSide_GentryA_diag_eq
import Theorems.Thm_Zeta23_PrimeSide_Pi_part_bound
import Theorems.Thm_Zeta23_PrimeSide_Setting_tau_mem
import Theorems.Thm_Zeta23_PrimeSide_lem_ends
import Theorems.Thm_Zeta23_PrimeSide_mu_abs_le_l
import Theorems.Thm_Zeta23_PrimeSide_mu_increment_bound
import Theorems.Thm_Zeta23_PrimeSide_mu_nonneg_eventually
import Theorems.Thm_Zeta23_PrimeSide_mu_part_bound
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_muP
import Theorems.Thm_Zeta23_PrimeSide_prop_mumu
import Theorems.Thm_Zeta23_PrimeSide_riemann_sum_monotone
import Theorems.Thm_Zeta23_PrimeSide_sum_P_part_bound

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

lemma LocalHypsCore.b_pos (hF : LocalHypsCore cϱ p F) : 0 < F.b := by
  linarith [hF.b_ge_half]

lemma LocalHypsCore.a_pos (hF : LocalHypsCore cϱ p F) : 0 < F.a := hF.b_pos.trans_le hF.b_le_a


















end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


















/-- The grid: `τ_k ∈ [T, 2T]` for `0 ≤ k < d` (§2.2 "τ_0,…,τ_{d−1} ∈ [T,2T)"), and `d ≤ LT/2π`. -/
lemma Setting.d_le (p : Setting) (h : 0 ≤ p.L * p.T) : (p.d : ℝ) ≤ p.L * p.T / (2 * π) :=
  Nat.floor_le (by positivity)

lemma Setting.d_eq_floor (p : Setting) (hL : 0 < p.L) : p.d = ⌊p.T / p.h⌋₊ := by
  simp only [Setting.d, Setting.h]
  congr 1
  field_simp

lemma Setting.tau_natCast (p : Setting) (k : ℕ) : p.tau k = p.T + k * p.h := by
  simp [Setting.tau]


end TraceAnalytic

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

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

section Results

variable (cϱ lam : ℝ)
/-! ## [prop:trace]  (§5.2) -/



/-! ## [lem:ends]  (§5.3), with [eq:Kdef], [eq:trG2int], [eq:Kbounds] -/

-- **[lem:ends]** is proved in Zeta23/PrimeSideA/Ends.lean:
-- `Zeta23.PrimeSide.lem_ends` (§5.3) — imported by this module.

/-! ## [eq:Msplit]  (§5.4) -/


/-! ## [prop:mumu]  (§5.4) -/

/-! **[prop:mumu]**, first form (§5.4, verbatim): `𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L)`.
(The second form `= (bLTℓ₁²/2π)(1+O(l⁻²)) + O(l² log L)` follows with [eq:muints] and is taken in
PrimeSideB.)  We write `log L` as in the paper; note `log L ≤ log l` since `λ ≤ 1`. -/
-- **[prop:mumu]** is proved in Zeta23/PrimeSideA/MuMu.lean:
-- `Zeta23.PrimeSide.prop_mumu` — imported by this module, so available here under the same name.

/-! ## [prop:cross]  (§5.4) -/

-- **[prop:cross] (i)** is proved in Zeta23/PrimeSideA/CrossMuP.lean:
-- `Zeta23.PrimeSide.prop_cross_muP` (§5.4: 𝓜[μ,P_X] ≪ l√X) — imported by this module.




end Results

/-!
## Contents
Proved in this file:
* eq_Msplit — [eq:Msplit]
* prop_cross_muPi / _PPi / _PiPi — [prop:cross] (ii)(iii)(iv)
* prop_trace_mu, prop_trace — **[prop:trace]** (μ-form and the paper's aL·N(T,2T) + O(L√X) form)
Proved in child files, imported here:
* prop_mumu      — [prop:mumu]     — Zeta23/PrimeSideA/MuMu.lean
* prop_cross_muP — [prop:cross](i) — Zeta23/PrimeSideA/CrossMuP.lean
* lem_ends       — [lem:ends]      — Zeta23/PrimeSideA/Ends.lean
-/

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)
set_option maxHeartbeats 1000000

theorem solution (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ| ≤ C * (p.L * Real.sqrt p.X)) := by
  obtain ⟨K, hK0, hK⟩ := mu_increment_bound hΓ
  obtain ⟨x₀, hx₀⟩ := hcheb.cheb1b
  obtain ⟨T₁, hT₁⟩ := mu_abs_le_l hΓ
  obtain ⟨τ₀, hτ₀0, hτ₀⟩ := mu_nonneg_eventually hΓ
  refine ⟨8 * K + 2 * |cϱ| * K + 44 * cϱ ^ 2 + 4 * π / lam + 245,
    max (max T₁ 4) (max (2 * π * Real.exp (|x₀| / lam)) (τ₀ + 1)), fun p F hplam hT hF => ?_⟩
  -- thresholds
  have hTa : max T₁ 4 ≤ p.T := (le_max_left _ _).trans hT
  have hTb : max (2 * π * Real.exp (|x₀| / lam)) (τ₀ + 1) ≤ p.T := (le_max_right _ _).trans hT
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hTa
  have hT4 : 4 ≤ p.T := (le_max_right _ _).trans hTa
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := (le_max_left _ _).trans hTb
  have hTτ : τ₀ + 1 ≤ p.T := (le_max_right _ _).trans hTb
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hL8 := hF.eight_le_L
  have hc4 := hF.four_le_cϱ
  have hc0 : 0 ≤ cϱ := by linarith
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact hTx)
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]; exact Real.one_le_exp hL.le |>.trans_eq rfl
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hh0 : 0 < p.h := by simp only [Setting.h]; positivity
  have hh1 : p.h ≤ 1 := by
    simp only [Setting.h]; rw [div_le_one hL]; linarith [Real.pi_lt_four]
  have hl1 := hF.one_le_l
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  -- the two taper integrals
  set I₁ := ∫ r, F.phiHat r ^ 2 * |r| with hI₁def
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂def
  have hI₁0 : 0 ≤ I₁ := integral_nonneg fun r => by positivity
  have hI₂0 : 0 ≤ I₂ := integral_nonneg fun r => by positivity
  have hI₁ : I₁ ≤ 8 + 2 * cϱ * p.L := by
    refine hF.integral_phiHat_sq_mul_abs_le.trans ?_
    have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) :=
      Real.log_le_self (by have := hF.one_le_w; positivity)
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num); linarith [hF.one_le_w]
    linarith
  have hI₂ : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]; exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  -- rewrite tr G̃ as a sum over range d
  have hsumFin : ∑ k : Fin p.d, GentryA p F k k = ∑ k ∈ Finset.range p.d, GentryA p F k k :=
    Fin.sum_univ_eq_sum_range (fun k => GentryA p F k k) p.d
  -- grid facts
  have hτ : ∀ k ∈ Finset.range p.d, p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := fun k hk =>
    p.tau_mem hL hT0.le hk
  -- decomposition of each diagonal entry
  set Gμ : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r) with hGμ
  set GPi : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r) with hGPi
  set GP : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r) with hGP
  have hdecomp : ∑ k ∈ Finset.range p.d, GentryA p F k k
      = ∑ k ∈ Finset.range p.d, Gμ k + ∑ k ∈ Finset.range p.d, GPi k
        + ∑ k ∈ Finset.range p.d, GP k := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact GentryA_diag_eq hΓ hF k (by linarith [(hτ k hk).1])
  -- (1) μ-part vs 2πaL μ(τ_k)
  have h1 : |∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
      Zeta23.mu (p.tau k)| ≤ p.d * ((K * I₁ + 10 * I₂) / p.T) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ k ∈ Finset.range p.d, |Gμ k - 2 * π * F.a * p.L * Zeta23.mu (p.tau k)|
        ≤ (K * I₁ + 10 * I₂) / p.T := by
      intro k hk
      have ht2 : 2 ≤ p.tau k := by linarith [(hτ k hk).1]
      refine (mu_part_bound hΓ hF hK ht2).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) hT0 (hτ k hk).1
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (2) Riemann sum: 2πaL Σ μ(τ_k) vs aL² ∫ μ
  have h2 : |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ| ≤ 4 * π * p.L * p.l := by
    have hR := riemann_sum_monotone (μ := Zeta23.mu) (T := p.T) hh0 (by linarith)
      (hΓ.monotoneOn.mono (fun x hx => by
        simp only [Set.mem_Ici] at hx ⊢; linarith))
      (fun x hx => hτ₀ x (by linarith))
    rw [← p.d_eq_floor hL] at hR
    have hsum : ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
        = ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h) := by
      refine Finset.sum_congr rfl fun k _ => by rw [Setting.tau_natCast]
    rw [hsum]
    have hid : 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h)
        - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ
        = F.a * p.L ^ 2 * (p.h * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h)
            - ∫ τ in p.T..(2 * p.T), Zeta23.mu τ) := by
      simp only [Setting.h]; field_simp
    rw [hid, abs_mul, abs_of_nonneg (by positivity)]
    have hμ2T : Zeta23.mu (2 * p.T) ≤ p.l := by
      have := hT₁ p hT₁' (2 * p.T) ⟨by linarith, le_rfl⟩
      exact (le_abs_self _).trans this
    have hμ2T0 : 0 ≤ Zeta23.mu (2 * p.T) := hτ₀ _ (by linarith)
    calc F.a * p.L ^ 2 * |p.h * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.T + k * p.h)
          - ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
        ≤ F.a * p.L ^ 2 * (2 * p.h * Zeta23.mu (2 * p.T)) := by gcongr
      _ ≤ 1 * p.L ^ 2 * (2 * p.h * p.l) := by gcongr
      _ = 4 * π * p.L * p.l := by simp only [Setting.h]; field_simp; ring
  -- (3) Π-part
  have h3 : |∑ k ∈ Finset.range p.d, GPi k|
      ≤ p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂) := by
    have hbound : ∀ k ∈ Finset.range p.d, |GPi k|
        ≤ (6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂ := by
      intro k hk
      have ht := (hτ k hk).1
      have ht2 : 2 ≤ p.tau k := by linarith
      have ht0 : 0 < p.tau k := by linarith
      refine (Pi_part_bound hF ht2).trans ?_
      have e1 : 6 * Real.sqrt p.X / p.tau k ≤ 6 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 ht
      have e2 : 12 * Real.sqrt p.X / p.tau k ^ 2 ≤ 12 * Real.sqrt p.X / p.T :=
        div_le_div_of_nonneg_left (by positivity) hT0 (by nlinarith)
      have e3 : 2 * π * F.a * p.L ≤ 2 * π * p.L := by
        have h1 : 2 * π * F.a ≤ 2 * π := mul_le_of_le_one_right (by positivity) ha1
        have h2 : (2 * π * F.a) * p.L ≤ (2 * π) * p.L := mul_le_mul_of_nonneg_right h1 hL.le
        linarith
      have b1 : 6 * Real.sqrt p.X / p.tau k * (2 * π * F.a * p.L)
          ≤ 6 * Real.sqrt p.X / p.T * (2 * π * p.L) :=
        mul_le_mul e1 e3 (by positivity) (by positivity)
      have b2 : 12 * Real.sqrt p.X / p.tau k ^ 2 * I₂
          ≤ 12 * Real.sqrt p.X / p.T * I₂ := mul_le_mul_of_nonneg_right e2 hI₂0
      linarith
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hbound)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (4) P-part
  have h4 : |∑ k ∈ Finset.range p.d, GP k| ≤ p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) := by
    refine (sum_P_part_bound hF).trans ?_
    exact mul_le_mul_of_nonneg_left (hx₀ _ hX)
      (div_nonneg (sq_nonneg _) (Real.log_nonneg one_le_two))
  -- d ≤ L T
  have hd : (p.d : ℝ) ≤ p.L * p.T := by
    refine (p.d_le (by positivity)).trans (div_le_self (by positivity) ?_)
    linarith [Real.pi_gt_three]
  have hdT : (p.d : ℝ) / p.T ≤ p.L := by rwa [div_le_iff₀ hT0]
  -- combine: |Σ G_kk − aL² ∫μ| ≤ …
  have hmain : |∑ k ∈ Finset.range p.d, GentryA p F k k
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
      ≤ p.L * (K * I₁ + 10 * I₂) + 4 * π * p.L * p.l
        + p.L * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂)
        + p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) := by
    rw [hdecomp]
    have e1 : p.d * ((K * I₁ + 10 * I₂) / p.T) ≤ p.L * (K * I₁ + 10 * I₂) := by
      rw [mul_div_assoc', div_le_iff₀ hT0]
      calc (p.d : ℝ) * (K * I₁ + 10 * I₂) ≤ (p.L * p.T) * (K * I₁ + 10 * I₂) := by
            gcongr
        _ = p.L * (K * I₁ + 10 * I₂) * p.T := by ring
    have e3 : p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂)
        ≤ p.L * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂) := by
      have : p.d * ((6 * Real.sqrt p.X / p.T) * (2 * π * p.L) + (12 * Real.sqrt p.X / p.T) * I₂)
          = (p.d / p.T) * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂) := by
        field_simp
      rw [this]; gcongr
    calc |∑ k ∈ Finset.range p.d, Gμ k + ∑ k ∈ Finset.range p.d, GPi k
          + ∑ k ∈ Finset.range p.d, GP k - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
        = |(∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
              Zeta23.mu (p.tau k))
            + (2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
              - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ)
            + ∑ k ∈ Finset.range p.d, GPi k + ∑ k ∈ Finset.range p.d, GP k| := by ring_nf
      _ ≤ |∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
              Zeta23.mu (p.tau k)|
            + |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, Zeta23.mu (p.tau k)
              - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
            + |∑ k ∈ Finset.range p.d, GPi k| + |∑ k ∈ Finset.range p.d, GP k| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by linarith [h1.trans e1, h2, h3.trans e3, h4]
  -- divide by L and pass to tr G̃
  have htr : trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ
      = p.L⁻¹ * (∑ k ∈ Finset.range p.d, GentryA p F k k
          - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ) := by
    simp only [trGtA, hsumFin]; field_simp
  -- final arithmetic: everything ≤ C · L√X
  set S := p.L * Real.sqrt p.X with hS
  have hS8 : 8 ≤ S := by nlinarith
  have hS1 : 1 ≤ S := by linarith
  have hLS : p.L ≤ S := by nlinarith
  have hlS : p.l ≤ S / lam := by
    rw [le_div_iff₀ hlam.1]
    have : p.l * lam = p.L := by rw [← hplam]; simp only [Setting.L]; ring
    rw [this]; exact hLS
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : 0 < Real.log 2 := by linarith
  have t1 : K * I₁ + 10 * I₂ ≤ (8 * K + 2 * |cϱ| * K + 80 + 20 * cϱ ^ 2) * S := by
    rw [abs_of_nonneg hc0]
    have v1 : K * I₁ ≤ K * (8 + 2 * cϱ * p.L) := by gcongr
    have v2 : 10 * I₂ ≤ 10 * (8 + 2 * cϱ ^ 2) := by linarith
    have u1 : 8 * K ≤ 8 * K * S := le_mul_of_one_le_right (by positivity) hS1
    have u2 : 2 * cϱ * K * p.L ≤ 2 * cϱ * K * S :=
      mul_le_mul_of_nonneg_left hLS (by positivity)
    have u3 : (80:ℝ) ≤ 80 * S := by linarith
    have u4 : 20 * cϱ ^ 2 ≤ 20 * cϱ ^ 2 * S := le_mul_of_one_le_right (by positivity) hS1
    nlinarith [mul_nonneg hc0 hK0]
  have t2 : 4 * π * p.l ≤ (4 * π / lam) * S := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam.1]
    have hls : p.l * lam ≤ S := by rw [← le_div_iff₀ hlam.1]; exact hlS
    calc 4 * π * p.l * lam = 4 * π * (p.l * lam) := by ring
      _ ≤ 4 * π * S := by gcongr
      _ = 4 * π * S := rfl
  have t3 : (6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂
      ≤ (160 + 24 * cϱ ^ 2) * S := by
    have e : (6 * Real.sqrt p.X) * (2 * π * p.L) = 12 * π * S := by rw [hS]; ring
    have f : (12 * Real.sqrt p.X) * I₂ ≤ 12 * (8 + 2 * cϱ ^ 2) * S := by
      calc (12 * Real.sqrt p.X) * I₂ ≤ (12 * Real.sqrt p.X) * (8 + 2 * cϱ ^ 2) := by gcongr
        _ = 12 * (8 + 2 * cϱ ^ 2) * (1 * Real.sqrt p.X) := by ring
        _ ≤ 12 * (8 + 2 * cϱ ^ 2) * (p.L * Real.sqrt p.X) := by gcongr; linarith
        _ = 12 * (8 + 2 * cϱ ^ 2) * S := by rw [hS]
    have hS0 : 0 ≤ S := by linarith
    have g : 12 * π * S ≤ 48 * S :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) hS0
    rw [e]; linarith
  have t4 : p.L / Real.log 2 * (3 * Real.sqrt p.X) ≤ 5 * S := by
    rw [hS, div_mul_eq_mul_div, div_le_iff₀ hlog2']
    have h5 : 3 * (p.L * Real.sqrt p.X) ≤ 5 * Real.log 2 * (p.L * Real.sqrt p.X) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hL.le hsX)
    linarith
  calc |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
      = p.L⁻¹ * |∑ k ∈ Finset.range p.d, GentryA p F k k
          - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ| := by
        rw [htr, abs_mul, abs_of_pos (inv_pos.2 hL)]
    _ ≤ p.L⁻¹ * (p.L * (K * I₁ + 10 * I₂) + 4 * π * p.L * p.l
        + p.L * ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂)
        + p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X)) := by gcongr
    _ = (K * I₁ + 10 * I₂) + 4 * π * p.l
        + ((6 * Real.sqrt p.X) * (2 * π * p.L) + (12 * Real.sqrt p.X) * I₂)
        + p.L / Real.log 2 * (3 * Real.sqrt p.X) := by field_simp
    _ ≤ (8 * K + 2 * |cϱ| * K + 80 + 20 * cϱ ^ 2) * S + (4 * π / lam) * S
        + (160 + 24 * cϱ ^ 2) * S + 5 * S := by linarith
    _ = (8 * K + 2 * |cϱ| * K + 44 * cϱ ^ 2 + 4 * π / lam + 245) * S := by ring
