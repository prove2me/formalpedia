-- Prove2me | Theorems.Thm_Zeta23_hasDerivAt_Zeta0Integral
-- name    : Zeta23_hasDerivAt_Zeta0Integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:39:33.265438+00:00
-- url     : https://prove2.me/theorems/53b7dc4c-4919-4eb2-9666-a110621030cc
-- title:
--   Differentiation under the integral sign for the Euler–Maclaurin tail integral of $\zeta$
-- statement:
--   Fix a positive integer $N$ and a complex number $s$ with $\mathrm{Re}\,s > 0$. For a real variable $x > 0$ and a complex exponent $w$, the power $x^{w}$ is the principal complex power, and $\lfloor x \rfloor$ denotes the integer floor of $x$ (cast into $\mathbb{C}$ in the integrand). Consider the tail integral
--   $$F(z) \;=\; \int_{N}^{\infty} \Bigl(\lfloor x \rfloor + \tfrac{1}{2} - x\Bigr)\, x^{-z-1}\, dx,$$
--   whose integrand involves the bounded sawtooth-type function $\lfloor x \rfloor + \tfrac12 - x$.
--
--   The theorem asserts that $F$ is complex differentiable at $s$ (in the sense of `HasDerivAt`), with derivative obtained by differentiating under the integral sign:
--   $$F'(s) \;=\; \int_{N}^{\infty} \Bigl(\lfloor x \rfloor + \tfrac{1}{2} - x\Bigr)\, x^{-s-1}\, \bigl(-\log x\bigr)\, dx.$$
--   Both integrals converge because the sawtooth factor is bounded and $x^{-\mathrm{Re}\,s - 1}$ (with or without a logarithmic factor) is integrable on $(N, \infty)$ when $\mathrm{Re}\,s > 0$.
--
--   In the module `Zeta23.FromPNTPlus.ZetaBounds`, this tail integral is the analytic ingredient of the modified zeta function $\zeta_0(N, s)$ (`riemannZeta0`), the truncated Euler–Maclaurin representation of $\zeta$. The lemma shows the integral term of $\zeta_0$ is holomorphic on $\mathrm{Re}\,s > 0$, and it feeds into `Zeta0EqZeta`, which identifies $\zeta_0(N, s) = \zeta(s)$ there for $s \neq 1$ — the representation used to prove the zeta bounds in the zero-density and explicit-formula parts of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ZetaBounds.lean#L948-L1037

import Batteries.Tactic.Lemma
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds

set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0
open MeasureTheory

theorem Zeta23_hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by sorry
