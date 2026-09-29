-- Prove2me | Theorems.Thm_SmoothedChebyshevDirichlet_aux_tsum_integral
-- name    : SmoothedChebyshevDirichlet_aux_tsum_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:02:28.481441+00:00
-- url     : https://prove2.me/theorems/d9f2ea50-3bb5-4358-aabf-1d9851b70604
-- title:
--   Sum–integral interchange for the smoothed Dirichlet-series integrand on a vertical line
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$, nonnegative on $(0, \infty)$, supported in $[1/2, 2]$, with mass one $\int_0^\infty F(x)\,dx/x = 1$. Fix $X > 0$, $\epsilon \in (0, 1)$, and $\sigma$ with $1 < \sigma \le 2$, and write $s = \sigma + it$ for points of the vertical line $\mathrm{Re}(s) = \sigma$. Let $\widetilde{1_\epsilon}$ be the smoothed cutoff built from $F$ and $\mathcal{M}$ its Mellin transform.
--
--   Then the integral over the vertical line and the sum over $n$ of the smoothed Dirichlet-series integrand may be interchanged:
--
--   $$\int_{-\infty}^{\infty} \sum_{n=1}^{\infty} \frac{\Lambda(n)}{n^{\sigma + it}}\, \mathcal{M}\big(\widetilde{1_\epsilon}\big)(\sigma + it)\, X^{\sigma + it} \, dt \;=\; \sum_{n=1}^{\infty} \int_{-\infty}^{\infty} \frac{\Lambda(n)}{n^{\sigma + it}}\, \mathcal{M}\big(\widetilde{1_\epsilon}\big)(\sigma + it)\, X^{\sigma + it} \, dt.$$
--
--   This Fubini–Tonelli step is the technical heart of the identity expressing the smoothed Chebyshev contour integral as the smoothed sum $\sum_n \Lambda(n)\, \widetilde{1_\epsilon}(n/X)$: absolute convergence comes from the convergence of $\sum \Lambda(n) n^{-\sigma}$ for $\sigma > 1$ together with the integrability of $\mathcal{M}(\widetilde{1_\epsilon})$ on the line. It is stated separately so the analytic bookkeeping is reusable and the main Perron-style theorem stays readable.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L118-L186

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow
set_option backward.isDefEq.respectTransparency false

theorem SmoothedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n) / (n : ℂ) ^ (σ + ↑t * I) *
        𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by sorry
