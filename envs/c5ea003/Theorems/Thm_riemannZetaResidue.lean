-- Prove2me | Theorems.Thm_riemannZetaResidue
-- name    : riemannZetaResidue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:45:21.941355+00:00
-- url     : https://prove2.me/theorems/ff6eb759-2d21-4775-956c-16a13fd757b5
-- title:
--   $\zeta$ has a simple pole of residue $1$ at $s=1$: boundedness of $\zeta(s) - (s-1)^{-1}$
-- statement:
--   There exists a neighborhood $U$ of $1 \in \mathbb{C}$ such that the difference between the Riemann zeta function and the model simple pole $(s-1)^{-1}$ has bounded norm on the punctured set $U \setminus \{1\}$: the set
--
--   $$\left\{\, \left\| \zeta(s) - \frac{1}{s-1} \right\| \;:\; s \in U \setminus \{1\} \,\right\}$$
--
--   is bounded above.
--
--   This is the quantitative form of the classical fact that $\zeta$ extends meromorphically with a single simple pole at $s = 1$ of residue $1$ (indeed $\zeta(s) - (s-1)^{-1}$ extends to an entire function, so it is in particular locally bounded).
--
--   In the PNT+ development this boundedness feeds the abstract nonvanishing lemma (`nonZeroOfBddAbove`) to conclude $\zeta \neq 0$ in a punctured neighborhood of $s=1$, and it anchors the residue computations that extract the main term of the Prime Number Theorem from contour integrals against $-\zeta'/\zeta$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L155-L161

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

theorem riemannZetaResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (ζ - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by sorry
