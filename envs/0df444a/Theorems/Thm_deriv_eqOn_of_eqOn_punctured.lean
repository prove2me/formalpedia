-- Prove2me | Theorems.Thm_deriv_eqOn_of_eqOn_punctured
-- name    : deriv_eqOn_of_eqOn_punctured
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:41:21.244509+00:00
-- url     : https://prove2.me/theorems/04044142-aa2b-4285-855f-aaaf2c8efa76
-- title:
--   Functions equal off a point have equal derivatives off that point
-- statement:
--   Let $f, g : \mathbb{C} \to \mathbb{C}$, let $U \subseteq \mathbb{C}$ be an open set, and let $p \in \mathbb{C}$. Suppose $f$ and $g$ agree on the punctured set $U \setminus \{p\}$. Then their derivatives also agree there:
--
--   $$f = g \text{ on } U \setminus \{p\} \quad \Longrightarrow \quad f' = g' \text{ on } U \setminus \{p\}.$$
--
--   The point is that $U \setminus \{p\}$ is itself open, so around each of its points the two functions coincide on a neighbourhood, and the derivative — a local notion — cannot distinguish them. No differentiability hypothesis is needed: at points where neither function is differentiable both derivatives are the junk value, and the local-equality argument still applies.
--
--   In the PNT+ zeta-bounds development this lemma is used in pole-removal arguments: $\zeta$ agrees with (main term) $+$ (holomorphic remainder) away from $s = 1$, and one needs the same identity for the derivatives on the punctured neighbourhood. It is fully generic and reusable for any pair of functions agreeing off a discrete point.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L165-L171

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

theorem deriv_eqOn_of_eqOn_punctured (f g : ℂ → ℂ) (U : Set ℂ) (p : ℂ)
    (hU_open : IsOpen U)
    (h_eq : EqOn f g (U \ {p})) :
    EqOn (deriv f) (deriv g) (U \ {p}) := by sorry
