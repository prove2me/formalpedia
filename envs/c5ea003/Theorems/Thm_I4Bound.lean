-- Prove2me | Theorems.Thm_I4Bound
-- name    : I4Bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:48:51.942254+00:00
-- url     : https://prove2.me/theorems/8d8f3684-dda4-49b3-8c2f-69b7b9177fea
-- title:
--   Bound $O\!\left(\frac{X \cdot X^{-A/\log^9 T}}{\varepsilon}\right)$ for the low horizontal segment $I_4$ near the real axis
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ be a $C^1$ smoothing function supported in $[1/2, 2]$. Fix $\sigma_2 \in (0,1)$ and assume the local holomorphy hypothesis: the logarithmic derivative $\zeta'/\zeta$ is holomorphic on the box $[\sigma_2, 2] \times i[-3, 3]$ with the point $s = 1$ removed. Fix also $A \in (0, 1/2]$. In the contour decomposition of the smoothed Chebyshev function, let
--   $$I_4(\nu, \varepsilon, X, \sigma_1, \sigma_2) = \frac{1}{2\pi i} \int_{\sigma_2}^{\sigma_1} F(\sigma - 3i)\, d\sigma$$
--   be the short horizontal segment at height $-3$ joining $\sigma_2$ to $\sigma_1$, where $F$ is the smoothed Chebyshev integrand.
--
--   Then there exist a constant $C \geq 0$ and a threshold $T_{\mathrm{lb}} > 3$ such that for all $X > 3$, all $\varepsilon \in (0,1)$, and all $T > T_{\mathrm{lb}}$, with $\sigma_1 = 1 - A/\log^9 T$:
--   $$\|I_4(\nu, \varepsilon, X, \sigma_1, \sigma_2)\| \leq \frac{C\, X \cdot X^{-A/\log^9 T}}{\varepsilon}.$$
--
--   On this fixed compact segment (away from the pole at $s=1$ and at bounded height) the factor $\zeta'/\zeta \cdot \mathcal{M}$ is bounded by compactness, and $|X^s| \le X^{\sigma_1}$ gives the same power saving $X^{-A/\log^9 T}$ as on the shifted vertical line; the threshold $T_{\mathrm{lb}}$ ensures $\sigma_1$ has entered the strip where these bounds apply.
--
--   Together with the bounds for $I_1, I_2, I_3$ and their mirror-image legs, this estimate completes the control of the deformed Perron contour for the smoothed Chebyshev function in the PNT+ project, yielding the Prime Number Theorem with an explicit error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L2484-L2854

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

theorem I4Bound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    {σ₂ : ℝ} (h_logDeriv_holo : LogDerivZetaIsHoloSmall σ₂) (hσ₂ : σ₂ ∈ Ioo 0 1)
    {A : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) :
    ∃ (C : ℝ) (_ : 0 ≤ C) (Tlb : ℝ) (_ : 3 < Tlb),
    ∀ (X : ℝ) (_ : 3 < X)
    {ε : ℝ} (_ : 0 < ε) (_ : ε < 1)
    {T : ℝ} (_ : Tlb < T),
    let σ₁ : ℝ := 1 - A / (Real.log T) ^ 9
    ‖I₄ SmoothingF ε X σ₁ σ₂‖ ≤ C * X * X ^ (- A / (Real.log T ^ 9)) / ε := by sorry
