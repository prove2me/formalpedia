-- Prove2me | Theorems.Thm_SmoothedChebyshevPull1
-- name    : SmoothedChebyshevPull1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:06:40.291309+00:00
-- url     : https://prove2.me/theorems/4a5ff1f6-beef-4010-b3e9-f7780776336e
-- title:
--   First contour pull: $\psi_\epsilon(X)$ as rectangle contour pieces plus the residue $\mathcal{M}(\widetilde{1_\epsilon})(1)\, X$ at $s = 1$
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$, nonnegative on $(0,\infty)$, supported in $[1/2,2]$, of multiplicative mass one; fix $\epsilon \in (0,1)$, $X > 3$, a height $T > 0$, and an abscissa $\sigma_1 \in (0, 1)$. Assume the logarithmic derivative $\zeta'/\zeta$ of the Riemann zeta function is holomorphic on the punctured box $[\sigma_1, 2] \times i[-T, T] \setminus \{1\}$ — that is, $\zeta$ has no zeros in this box, as furnished by a zero-free region.
--
--   Then the smoothed Chebyshev function, initially a contour integral along a vertical line $\mathrm{Re}(s) = \sigma_0 > 1$, can be pulled to the boundary of the box, picking up exactly the contribution of the pole of $-\zeta'/\zeta$ at $s = 1$:
--
--   $$\psi_\epsilon(X) \;=\; I_1 - I_2 + I_{37} + I_8 + I_9 \;+\; \mathcal{M}\big(\widetilde{1_\epsilon}\big)(1)\cdot X,$$
--
--   where $I_1, I_9$ are the two tails of the original vertical line above height $T$ and below height $-T$, $I_2, I_8$ are the horizontal segments at heights $\pm T$ connecting $\mathrm{Re}(s) = \sigma_0$ to $\mathrm{Re}(s) = \sigma_1$, and $I_{37}$ is the remaining truncated vertical integral on the line $\mathrm{Re}(s) = \sigma_1$ (all built from the integrand $-\tfrac{\zeta'}{\zeta}(s)\, \mathcal{M}(\widetilde{1_\epsilon})(s)\, X^s / (2\pi i)$).
--
--   This is the residue-extraction step of the smoothed Prime Number Theorem: the term $\mathcal{M}(\widetilde{1_\epsilon})(1) \cdot X = (1 + O(\epsilon))X$ is the main term, and the five remaining contour pieces are error integrals to be estimated using bounds on $\zeta'/\zeta$ in the zero-free region and the decay of the Mellin transform.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L825-L994

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

theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by sorry
