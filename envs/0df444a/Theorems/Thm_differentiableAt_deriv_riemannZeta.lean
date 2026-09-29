-- Prove2me | Theorems.Thm_differentiableAt_deriv_riemannZeta
-- name    : differentiableAt_deriv_riemannZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:38:08.159049+00:00
-- url     : https://prove2.me/theorems/5b637ef9-9d5e-43f0-b95c-24f748e86403
-- title:
--   The derivative $\zeta'$ of the Riemann zeta function is differentiable away from $s = 1$
-- statement:
--   Let $s \in \mathbb{C}$ with $s \neq 1$. Then the derivative $\zeta'$ of the Riemann zeta function is complex differentiable at $s$:
--
--   $$s \neq 1 \implies \zeta' \text{ is differentiable at } s.$$
--
--   Since $\zeta$ is holomorphic on $\mathbb{C} \setminus \{1\}$ (its only singularity being the simple pole at $s = 1$), it is in fact infinitely differentiable there, and in particular $\zeta'$ is itself holomorphic on the same domain. This lemma records that fact at the level of a single point.
--
--   This is a basic regularity ingredient used throughout zeta-function estimates: whenever one manipulates the logarithmic derivative $\zeta'/\zeta$, differentiates zeta-related integrands, or applies residue-type arguments near $s = 1$, differentiability of $\zeta'$ off the pole is required.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L150-L152

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

theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by sorry
