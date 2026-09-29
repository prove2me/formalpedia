-- Prove2me | Theorems.Thm_Zeta23_isPathConnected_aux
-- name    : Zeta23_isPathConnected_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:40:04.642284+00:00
-- url     : https://prove2.me/theorems/cd890556-ebf6-4ed6-aba8-eb27d19508ff
-- title:
--   Path-connectedness of the slit right half-plane $\{\mathrm{Re}\,z > 0\} \setminus \{1\}$
-- statement:
--   Consider the subset of the complex plane
--   $$U \;=\; \{\, z \in \mathbb{C} \;:\; z \neq 1 \text{ and } \mathrm{Re}\,z > 0 \,\},$$
--   the open right half-plane with the single point $1$ removed.
--
--   The theorem asserts that $U$ is path-connected: any two points of $U$ can be joined by a continuous path lying entirely inside $U$. The proof takes $2$ as a base point and connects every $w \in U$ to it by one or two straight-line segments, detouring through $1 + i$ when $w$ is real (so that the segment avoids the puncture at $1$).
--
--   In the module `Zeta23.FromPNTPlus.ZetaBounds` this topological fact is used by `Zeta0EqZeta`: since the punctured half-plane $U$ is open and connected, the identity theorem for analytic functions applies on it, and the modified zeta function $\zeta_0(N, \cdot)$ (`riemannZeta0`, the truncated Euler–Maclaurin representation) — which agrees with the Riemann zeta function on $\mathrm{Re}\,s > 1$ — must agree with $\zeta$ on all of $U$. That identity underlies the growth estimates for $\zeta$ and $\zeta'$ used elsewhere in the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ZetaBounds.lean#L1095-L1148

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

theorem Zeta23_isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by sorry
