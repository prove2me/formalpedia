-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_Kinf_sub_Kfun_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:41:32.636179+00:00
-- url     : https://prove2.me/submissions/a3207535-cc5d-43a5-bec9-4ee9165768a8

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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Theorems.Thm_Zeta23_PrimeSide_hasSum_Kout

-- from Zeta23.PrimeSideA.EndsCore
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (§5, §5.3 of the paper), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

TARGET (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)))

PAPER (§5.3, verbatim): "For T ≥ T₀,  tr G̃² = 𝓜 + O(L l log l (l² + X)),
  𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'."

ROUTE (paper's, §5.3, with two simplifications that only change absolute constants):
* [eq:trG2int]  L² tr G̃² = Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν(τ)ν(τ') dτdτ',
  K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k)φ̂(τ'−τ_k) [eq:Kdef]  — here a product of two integrals and a
  FINITE sum, so no Fubini beyond ∫(f)·∫(g) = ∬ f⊗g.
* K_∞ := Σ_{k∈ℤ} φ̂(τ−τ_k)φ̂(τ'−τ_k) = L Φ(τ−τ') by [lem:poisson] (LocalHyps.poisson), so
  ∬_{I×I} K_∞² νν' = L² 𝓜, and  L²(tr G̃² − 𝓜)·L² … precisely:
  Σ G² − L²𝓜·… = 𝓔₁ + 𝓔₂,  𝓔₁ := ∬_{I×I}(K² − K_∞²)νν',  𝓔₂ := ∬_{ℝ²∖I×I} K²νν'.
* [eq:Kbounds]  |K|, |K_∞| ≤ L² (paper: aL²; a ≤ 1);  |K_out| = |K_∞ − K| handled by the
  weighted AM–GM  |Σ_{k∉[0,d)} a_k b_k| ≤ ½(s ρ(τ) + ρ(τ')/s), ρ(τ) := Σ_{k∉[0,d)} φ̂(τ−τ_k)²
  = aL² − Σ_{k<d} φ̂(τ−τ_k)² (Poisson diagonal — a FINITE expression), with s := g(τ')/g(τ),
  g := (1 + dist(·,∂I))⁻².  This replaces the paper's (∫_I ψ_k)²-sum (§5.3) and gives
  |𝓔₁| ≤ 2L²B²(∫_I ρ/g)(∫_I g) ≪ L²B²·L·l ≤ L³B² l log l  — within the lemma's error (the paper
  gets L³B² log L here; the slack l is free since 𝓔₂ is the dominant term anyway).
* 𝓔₂ exactly as the paper (§5.3): |𝓔₂| ≤ 2L² Σ_{k<d}(∫_{I^c}ψ_k|ν|)(∫_ℝ ψ_k|ν|),
  second factor ≤ 3Ψ₀B, Σ_k first factor = ∫_{I^c}|ν|σ ≪ BLl via the grid bound
  σ(τ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ψ, σ ≤ d ψ(Δ); for the far range we use log⁺x ≤ 2√x instead of
  integrating logarithms (constants only).
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X: Zeta23/PiFacts.lean
  (from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

FILE LAYOUT:
  EndsCore.lean (this file) — defs, continuity/integrability, [eq:trG2int],
     decomposition, ψ toolkit, [eq:Kbounds] pointwise;
  EndsE1.lean — calE1_bound;   EndsE2.lean (1-D estimates N1/N2 in EndsNu.lean,
     weights in EndsWeighted.lean) — calE2_bound;
  Ends.lean — assembly lem_ends' / lem_ends (proved from the two bounds).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-! The ψ majorant `psiA cϱ p r = min(L, 2/|r|, c_ϱ/(w r²))` [eq:psidef] and the [eq:psiints]
facts (psi_integrable, psi_sq_integrable, integral_psi_Ioi_le, integral_psi_sq_le, phiHat_le_psi,
Phi_le_psi) are in Zeta23/PrimeSideA (`LocalHyps`). -/



variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)

/-! ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for a free
`B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p` (bridges by `rfl`). -/





/-! ## [eq:Kdef] -/




/-! All double integrals below are integrals over `ℝ × ℝ` w.r.t. `volume` (= `volume.prod
volume`), restricted to `I ×ˢ I` or its complement where indicated — the same spelling as
`Mform` in Zeta23/PrimeSideA/Defs.lean. -/






variable {p F ν}

section Structure
variable {B : ℝ}
/-! ## [eq:trG2int] and the decomposition -/







/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/


















end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}























end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


lemma sum_Ico_int_eq (p : Setting) (F : LocalFun) (τ : ℝ) :
    ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = ∑ k : Fin p.d, F.phiHat (τ - p.tau (k : ℕ)) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => F.phiHat (τ - p.tau (n : ℕ)) ^ 2) p.d]
  rw [show Finset.Ico (0:ℤ) (p.d : ℤ) = (Finset.range p.d).image (fun n : ℕ => (n : ℤ)) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hd⟩
      exact ⟨k.toNat, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega]
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]

lemma hasSum_total (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (F.a * p.L ^ 2) := by
  have h := hF.poisson τ τ
  rw [sub_self, hF.Phi_zero] at h
  have h2 : HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (p.L * (F.a * p.L)) := by
    refine HasSum.congr_fun h fun k => ?_
    rw [sq]
  rwa [show p.L * (F.a * p.L) = F.a * p.L ^ 2 by ring] at h2


/-- `ρ(τ) = Σ_{k∉[0,d)} φ̂(τ−τ_k)²` as a `HasSum` over the complement of `range d` in ℤ
(from LocalHyps.poisson τ τ and Phi_zero). -/
theorem hasSum_rho (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} => F.phiHat (τ - p.tau k) ^ 2)
      (rho p F τ) := by
  have htot := hasSum_total hF τ
  refine (Finset.hasSum_compl_iff (f := fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2)
    (Finset.Ico (0:ℤ) (p.d : ℤ))).2 ?_
  have he : rho p F τ + ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = F.a * p.L ^ 2 := by
    unfold rho
    rw [sum_Ico_int_eq]
    ring
  rw [he]
  exact htot




/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/



/-- termwise weighted AM–GM: `|a b| ≤ (s a² + b²/s)/2` for `s > 0`. -/
lemma abs_mul_le_weighted (a b : ℝ) {s : ℝ} (hs : 0 < s) :
    |a * b| ≤ (s * a ^ 2 + b ^ 2 / s) / 2 := by
  rw [abs_mul]
  have h : 0 ≤ (s * |a| - |b|) ^ 2 / s := by positivity
  have e : (s * |a| - |b|) ^ 2 / s = s * a ^ 2 + b ^ 2 / s - 2 * (|a| * |b|) := by
    have ha := sq_abs a
    have hb := sq_abs b
    field_simp
    nlinarith [ha, hb]
  linarith [e ▸ h]


end Kbounds


end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)
variable {p F ν}
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem solution (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) {s : ℝ} (hs : 0 < s) :
    |Kinf p F τ τ' - Kfun p F τ τ'| ≤ (s * rho p F τ + rho p F τ' / s) / 2 := by
  set f : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} → ℝ :=
    fun k => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k) with hf
  have hK := hasSum_Kout hF τ τ'
  have hρ := hasSum_rho hF τ
  have hρ' := hasSum_rho hF τ'
  -- majorant
  have hmaj : HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} =>
      (s * F.phiHat (τ - p.tau k) ^ 2 + F.phiHat (τ' - p.tau k) ^ 2 / s) / 2)
      ((s * rho p F τ + rho p F τ' / s) / 2) :=
    ((hρ.mul_left s).add (hρ'.div_const s)).div_const 2
  have hle : ∀ k, |f k| ≤ (s * F.phiHat (τ - p.tau k) ^ 2 + F.phiHat (τ' - p.tau k) ^ 2 / s) / 2 :=
    fun k => abs_mul_le_weighted _ _ hs
  have habs : Summable (fun k => |f k|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hmaj.summable
  rw [← hK.tsum_eq]
  calc |∑' k, f k| ≤ ∑' k, |f k| := by
        have := norm_tsum_le_tsum_norm (f := f) (by simpa [Real.norm_eq_abs] using habs)
        simpa [Real.norm_eq_abs] using this
    _ ≤ (s * rho p F τ + rho p F τ' / s) / 2 :=
        hasSum_le hle habs.hasSum hmaj
