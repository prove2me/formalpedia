-- Prove2me | Theorems.Thm_SmoothedChebyshevDirichlet_aux_integrable
-- name    : SmoothedChebyshevDirichlet_aux_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:37:43.353543+00:00
-- url     : https://prove2.me/theorems/c1b3c757-c1e8-4a01-9352-619671d5f2d5
-- title:
--   Integrability of $t \mapsto \mathcal{M}(\widetilde{1_\epsilon})(\sigma + it)$ on vertical lines with $1 < \sigma \le 2$
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$, nonnegative on $(0, \infty)$, supported in $[1/2, 2]$, with multiplicative mass one $\int_0^\infty F(x)\,dx/x = 1$; fix $\epsilon \in (0,1)$ and a real $\sigma$ with $1 < \sigma \le 2$. Let $\widetilde{1_\epsilon}$ be the smoothed cutoff built from $F$ and $\mathcal{M}$ the Mellin transform.
--
--   Then the Mellin transform of the smoothed cutoff is (absolutely) integrable along the vertical line $\mathrm{Re}(s) = \sigma$:
--
--   $$t \;\longmapsto\; \mathcal{M}\big(\widetilde{1_\epsilon}\big)(\sigma + i t) \quad \text{is integrable on } \mathbb{R}.$$
--
--   The point is the decay in the vertical direction: because $\widetilde{1_\epsilon}$ is $C^1$ and compactly supported away from $0$, integration by parts in the Mellin integral gains a factor $1/|s|$ (indeed $1/|s|^2$ with two derivatives in $\epsilon$-dependent form), which makes the line integral defining the smoothed Chebyshev function absolutely convergent. This integrability is the hypothesis needed both to define $\psi_\epsilon(X)$ and to justify the Fubini-type interchanges in its evaluation as a Dirichlet sum.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L83-L112

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

theorem SmoothedChebyshevDirichlet_aux_integrable {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1)
    {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) :
    MeasureTheory.Integrable
      (fun (y : ℝ) ↦ 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + y * I)) := by sorry
