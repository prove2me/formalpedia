-- Prove2me | solution 1 for Zeta23.RvM.im_integral_le_two_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:59:05.485332+00:00
-- url     : https://prove2.me/submissions/26806f6b-d591-486e-adca-07e3a953803d

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_BacklundDefs
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_RvM_ReZeroCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

-- from Zeta23.RvM.ZetaGrowth
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/ZetaGrowth.lean — growth of ζ in vertical strips (consumed by the Landau/Jensen
local zero count and the Backlund S(T) bound).

CONTENT:
* `norm_riemannZeta_le_of_re_pos` — the explicit half-plane bound
      ‖ζ(s)‖ ≤ 1/2 + 1/‖1 − s‖ + ‖s‖ / Re s        (0 < Re s, s ≠ 1),
  from the N = 1 case of the summation-by-parts representation
      ζ(s) = Σ_{n≤N} n^{-s} − N^{1−s}/(1−s) − N^{−s}/2 + s ∫_N^∞ (⌊x⌋ + 1/2 − x) x^{−s−1} dx
  [Tit86, (2.1.4) / §2.1], which is `riemannZeta0` / `Zeta23_Zeta0EqZeta` in the PrimeNumberTheoremAnd
  port Zeta23/FromPNTPlus/ZetaBounds.lean (Apache-2.0, see README § Provenance).
* `riemannZeta_linear_growth` — for every δ > 0:  ‖ζ(σ+it)‖ ≤ (5/2 + δ⁻¹)·|t|  (σ ≥ δ, |t| ≥ 1)
  [Tit86, §5.1: ζ(s) = O(|t|) uniformly in σ ≥ δ], and the ∃-constant corollaries
  (`zeta_growth`, `zeta_growth_quarter`).
* `norm_riemannZeta_sub_one_le` — ‖ζ(s) − 1‖ ≤ π²/6 − 1 for Re s ≥ 2, hence the two-sided bounds
  0 < 2 − π²/6 ≤ ‖ζ(s)‖ ≤ π²/6 there (the Jensen/Landau disc centre 2 + it needs ζ ≠ 0 and a
  lower bound at the centre) [Tit86, §9.2 uses |ζ(2+iT)| ≥ … > 0].
* `analyticOnNhd_riemannZeta` — ζ is analytic on any set avoiding 1 (Mathlib's
  differentiableAt_riemannZeta, repackaged for the Jensen hypotheses).

NOT here: anything for Re s ≤ 0 (that needs the functional equation + Γ-ratio growth, i.e.
Stirling); no consumer in this repository needs it (σ ≥ 1/4 suffices).
-/

open Complex Set MeasureTheory Real

noncomputable section

namespace Zeta23
namespace RvM

/-! ## Analyticity away from the pole -/

/-- ζ is analytic on a neighbourhood of every set not containing 1. -/
theorem analyticOnNhd_riemannZeta {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    AnalyticOnNhd ℂ riemannZeta S := by
  have h : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) isOpen_compl_singleton
  exact h.mono (Set.subset_compl_singleton_iff.mpr hS)

/-! ## The half-plane bound  [Tit86, (2.1.4) with N = 1] -/


/-! ## Linear growth in σ ≥ δ  [Tit86, §5.1] -/






/-! ## Bounds on Re s ≥ 2 (the Jensen disc centre)  -/









end RvM
end Zeta23
end
end

-- from Zeta23.RvM.Backlund
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Backlund.lean — Backlund's bound for the horizontal variation of arg ζ, and the trivial
vertical side σ = 2. Consumed by Zeta23/RvM/Statement.lean, which proves
  N(T₁,T₂) = ∫_{T₁}^{T₂} μ + (1/π)·Im ∫_L ζ'/ζ ds,  L = ½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂
for non-ordinate heights and assembles RvM.main from GammaFacts.int_mu + the two bounds below.

* `backlund_horizontal` [Tit86 §9.4, Backlund 1918]: for T large and not the ordinate of a zero,
    |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ C log T.
  Route: g(z) := (ζ(z+iT) + conj ζ(z̄+iT))/2 is analytic near the disc |z−2| ≤ 1.9 and equals
  Re ζ(σ+iT) for real σ; g(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 0; ZerosBound (PNT+ port, unit disc,
  r = 0.8, R = 0.9 after scaling by 1.9) + Zeta23.RvM.zeta_growth (δ = 0.2) give
  #{σ ∈ [½,2] : Re ζ(σ+iT) = 0} ≤ C log T; on each of the ≤ m+1 subintervals where Re ζ(σ+iT)
  has constant sign, Complex.log ∘ (±ζ(·+iT)) is a primitive of ζ'/ζ with |Im| ≤ π.
* `vertical_two`: |Im (I·∫_{T₁}^{T₂} ζ'/ζ(2+it) dt)| ≤ π — log ζ is a primitive on σ ≥ 2
  (‖ζ − 1‖ ≤ π²/6 − 1 < 1 there, Zeta23.RvM.norm_riemannZeta_sub_one_le), and
  |arg ζ(2+it)| ≤ π/2 since Re ζ(2+it) > 0.
-/

open Complex Set MeasureTheory Real intervalIntegral

/- INSTANCE HYGIENE: `Zeta23.FromPNTPlus.StrongPNTPrefix` transitively imports
`Mathlib.Algebra.Lie.OfAssociative`, whose instance `LieAlgebra.ofAssociativeAlgebra` offers a second
(non-reducibly-defeq) route to `Module ℝ ℂ`; combined with this file's other imports that makes
`ContinuousSMul ℝ ℂ` — hence every `HasDerivAt (f : ℝ → ℂ)` — fail to synthesize (diagnosed
with `trace.Meta.synthInstance`).  Lie algebras are never used here. -/
attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23
namespace RvM


/-! ## The horizontal side, calculus half: variation of the argument

Fix a height `T ≠ 0` with `ζ ≠ 0` on the segment `[1/2, 2] + iT`.  If `Re ζ(σ+iT)` has no zero on an
open subinterval `(u,v)`, it has constant sign `ε` there (IVT), `log(ε ζ(σ+iT))` is a primitive of
`ζ'/ζ(σ+iT)` on `[u,v]` (at the endpoints `ε ζ` is `≥ 0` in real part and `≠ 0`, so still in the
slit plane), hence `|Im ∫_u^v ζ'/ζ| ≤ 2π`.  Splitting `[1/2,2]` at the finitely many zeros of
`Re ζ(σ+iT)` (the set `reZeroSet T`, counted by the Jensen bound `reZeroSet_card_le`) gives
`|Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ 2π (#reZeroSet T + 1)` — by induction on the number of zeros inside
the interval (no sorting needed). -/

section Variation

variable {T : ℝ}

lemma ofReal_add_mul_I_ne_one (hT : T ≠ 0) (σ : ℝ) : (σ : ℂ) + T * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hT this

/-- `σ ↦ ζ(σ+iT)` has derivative `ζ'(σ+iT)` in the real variable `σ`. -/
lemma hasDerivAt_riemannZeta_horizontal (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => riemannZeta (σ + T * I)) (deriv riemannZeta (σ + T * I)) σ := by
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (σ + T * I)) (σ + T * I) :=
    (differentiableAt_riemannZeta (ofReal_add_mul_I_ne_one hT σ)).hasDerivAt
  have hγ : HasDerivAt (fun σ : ℝ => (σ : ℂ) + T * I) 1 σ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt
    simpa using h1.add_const ((T : ℂ) * I)
  exact (hζ.comp σ hγ).congr_deriv (mul_one _)

lemma continuous_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => riemannZeta (σ + T * I)) :=
  continuous_iff_continuousAt.mpr fun σ => (hasDerivAt_riemannZeta_horizontal hT σ).continuousAt

lemma continuous_deriv_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => deriv riemannZeta (σ + T * I)) := by
  have hγ : Continuous (fun σ : ℝ => (σ : ℂ) + T * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  exact hA.deriv.continuousOn.comp_continuous hγ (fun σ => ofReal_add_mul_I_ne_one hT σ)

/-- `σ ↦ ζ'/ζ(σ+iT)` is continuous on `[1/2,2]` when ζ has no zero on that segment. -/
lemma continuousOn_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    ContinuousOn (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) (Set.Icc (1/2 : ℝ) 2) := by
  have h : ContinuousOn (fun σ : ℝ => deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I))
      (Set.Icc (1/2 : ℝ) 2) :=
    (continuous_deriv_riemannZeta_horizontal hT).continuousOn.div
      (continuous_riemannZeta_horizontal hT).continuousOn hnz
  exact h.congr (fun σ _ => by rw [logDeriv_apply])

lemma intervalIntegrable_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : u ∈ Set.Icc (1/2 : ℝ) 2) (hv : v ∈ Set.Icc (1/2 : ℝ) 2) :
    IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) volume u v :=
  ((continuousOn_logDeriv_horizontal hT hnz).mono
    (Set.uIcc_subset_Icc hu hv)).intervalIntegrable




end Variation

/-! ## Assembly of Backlund's bound from (J) = `reZeroSet_card_le`  and (V) -/






/-! ## The vertical side σ = 2 -/






end RvM
end Zeta23
end
open Complex Set MeasureTheory Real intervalIntegral
open Zeta23
open RvM
variable {T : ℝ}

theorem solution (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : 1/2 ≤ u) (huv : u < v) (hv : v ≤ 2)
    (hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0) :
    |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im| ≤ 2 * Real.pi := by
  set w : ℝ → ℂ := fun σ => riemannZeta (σ + T * I) with hwdef
  have hwc : Continuous w := continuous_riemannZeta_horizontal hT
  have huI : u ∈ Set.Icc (1/2 : ℝ) 2 := ⟨hu, by linarith⟩
  have hvI : v ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, hv⟩
  have hsub : Set.Icc u v ⊆ Set.Icc (1/2 : ℝ) 2 := Set.Icc_subset_Icc hu hv
  -- the sign ε ∈ {±1} of Re w at the midpoint
  set m : ℝ := (u + v) / 2 with hmdef
  have hm : m ∈ Set.Ioo u v := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  set ε : ℝ := if 0 < (w m).re then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by by_cases h : 0 < (w m).re <;> simp [hεdef, h]
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hεm : 0 < ε * (w m).re := by
    by_cases h : 0 < (w m).re
    · simp [hεdef, h]
    · have h' : (w m).re < 0 := lt_of_le_of_ne (not_lt.mp h) (hno m hm)
      simp only [hεdef, if_neg h]; linarith
  -- g := ε · Re w is continuous and, by the IVT, positive on all of (u,v)
  set g : ℝ → ℝ := fun x => ε * (w x).re with hgdef
  have hg : Continuous g := continuous_const.mul (Complex.continuous_re.comp hwc)
  have hpos : ∀ σ ∈ Set.Ioo u v, 0 < g σ := by
    intro σ hσ
    by_contra hneg
    have hσne : g σ ≠ 0 := mul_ne_zero hε0 (hno σ hσ)
    have hσneg : g σ < 0 := lt_of_le_of_ne (not_lt.mp hneg) hσne
    have hIcc : Set.uIcc σ m ⊆ Set.Ioo u v := Set.ordConnected_Ioo.uIcc_subset hσ hm
    have h0 : (0 : ℝ) ∈ Set.uIcc (g σ) (g m) :=
      Set.mem_uIcc.mpr (Or.inl ⟨hσneg.le, hεm.le⟩)
    obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hg.continuousOn h0
    exact mul_ne_zero hε0 (hno x (hIcc hx)) hx0
  -- by continuity, g ≥ 0 on the closed interval
  have hnonneg : ∀ σ ∈ Set.Icc u v, 0 ≤ g σ := by
    have hcl : IsClosed {x | 0 ≤ g x} := isClosed_le continuous_const hg
    have : Set.Icc u v ⊆ {x | 0 ≤ g x} := by
      rw [← closure_Ioo huv.ne]
      exact hcl.closure_subset_iff.mpr (fun x hx => (hpos x hx).le)
    exact fun σ hσ => this hσ
  -- hence ε·w stays in the slit plane on [u,v]
  have hslit : ∀ σ ∈ Set.Icc u v, (ε : ℂ) * w σ ∈ Complex.slitPlane := by
    intro σ hσ
    rw [Complex.mem_slitPlane_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    rcases (hnonneg σ hσ).lt_or_eq with h | h
    · exact Or.inl h
    · right
      intro him
      have hre : (w σ).re = 0 := by
        rcases mul_eq_zero.mp h.symm with h1 | h1
        · exact absurd h1 hε0
        · exact h1
      have him' : (w σ).im = 0 := by
        rcases mul_eq_zero.mp him with h1 | h1
        · exact absurd h1 hε0
        · exact h1
      exact hnz σ (hsub hσ) (Complex.ext hre him')
  -- Φ := log(ε·w) is a primitive of ζ'/ζ(σ+iT) on [u,v]
  have hderiv : ∀ σ ∈ Set.uIcc u v, HasDerivAt (fun x : ℝ => Complex.log ((ε : ℂ) * w x))
      (logDeriv riemannZeta (σ + T * I)) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le huv.le] at hσ
    have hwσ : w σ ≠ 0 := hnz σ (hsub hσ)
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0
    have h1 := (hasDerivAt_riemannZeta_horizontal hT σ).const_mul (ε : ℂ)
    have h2 := (Complex.hasDerivAt_log (hslit σ hσ)).comp σ h1
    have e : ((ε : ℂ) * w σ)⁻¹ * ((ε : ℂ) * deriv riemannZeta (σ + T * I))
        = logDeriv riemannZeta (σ + T * I) := by
      rw [logDeriv_apply, show riemannZeta ((σ : ℂ) + T * I) = w σ from rfl]
      field_simp
    rw [e] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_logDeriv_horizontal hT hnz huI hvI),
    Complex.sub_im, Complex.log_im, Complex.log_im]
  calc |((ε : ℂ) * w v).arg - ((ε : ℂ) * w u).arg|
      ≤ |((ε : ℂ) * w v).arg| + |((ε : ℂ) * w u).arg| := abs_sub _ _
    _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
    _ = 2 * Real.pi := by ring
