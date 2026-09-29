-- Prove2me | Theorems.Thm_ResidueOfTendsTo
-- name    : ResidueOfTendsTo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:44:55.201259+00:00
-- url     : https://prove2.me/theorems/e0c236b7-8d84-4466-9505-1e6405e5c4a0
-- title:
--   From the limit $(s-p)f(s)\to A$ to a bounded principal-part remainder near a simple pole
-- statement:
--   Let $f\colon\mathbb{C}\to\mathbb{C}$ be holomorphic on $U\setminus\{p\}$, where $U$ is a neighborhood of the point $p\in\mathbb{C}$. Assume the rescaled limit exists:
--
--   $$\lim_{\substack{s\to p\\ s\ne p}} (s-p)\,f(s) \;=\; A$$
--
--   for some $A\in\mathbb{C}$. Then $f$ differs from the principal part $\frac{A}{s-p}$ by a bounded function near $p$: there exists a neighborhood $V$ of $p$ such that
--
--   $$\sup_{s\in V\setminus\{p\}}\ \left| f(s) - \frac{A}{s-p} \right| \;<\; \infty.$$
--
--   The content is a Riemann-removable-singularity argument: the limit hypothesis says $f$ has at worst a simple pole at $p$ with residue $A$, and holomorphy on the punctured neighborhood upgrades the soft limit statement to actual boundedness of the remainder $f-\frac{A}{s-p}$ on a punctured neighborhood.
--
--   This lemma is the entry point of the development's residue calculus: natural hypotheses about poles (e.g. $(s-1)\zeta(s)\to 1$, so $-\zeta'/\zeta$ has residue $1$ at $s=1$) arrive as limits, and this converts them into the bounded-remainder form consumed by the rectangle residue theorem to extract main terms of contour integrals.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L36-L140

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

theorem ResidueOfTendsTo {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (hU : U ∈ 𝓝 p)
    (hf : HolomorphicOn f (U \ {p}))
    {A : ℂ}
    (h_limit : Tendsto (fun s ↦ (s - p) * f s) (𝓝[≠] p) (𝓝 A)) :
    ∃ V ∈ 𝓝 p,
    BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (V \ {p})) := by sorry
