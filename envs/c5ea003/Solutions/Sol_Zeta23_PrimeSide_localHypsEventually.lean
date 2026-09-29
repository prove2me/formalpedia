-- Prove2me | solution 1 for Zeta23.PrimeSide.localHypsEventually
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:09:34.141842+00:00
-- url     : https://prove2.me/submissions/699fc333-3abc-477f-b7a8-b9fb2add9446

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_Taper_Basic
import Definitions.Def_Zeta23_Taper_Params
import Theorems.Thm_Zeta23_PrimeSide_localHyps_concrete

-- from Zeta23.PrimeSideA.Bridge
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Bridge: the concrete taper data satisfy the abstract prime-side hypotheses `LocalHyps`

The §5 layer (`Zeta23/PrimeSideA.lean`) is proved for abstract data
`p : Setting = (T, λ, w)`, `F : LocalFun = (φ̂, Φ, A_φ, g, a, b)` under `LocalHyps cϱ p F` — the list
of test-family facts [eq:psidef], [eq:psiints], [eq:abdef], [eq:gbounds], [eq:PhigA], [eq:Phi2FT],
[lem:poisson], [eq:PiPfacts] used in §5.  Here:

* `localHyps_concrete` — every `LocalHyps` field for the concrete data, from `Taper.lean`,
  `Poisson.lean` ([lem:poisson]) and `PiFacts.lean`, with
  `cϱ := P.crho = c_ϱ` [eq:phinorms]; hence `localHypsEventually : LocalHypsEventually P.crho P`;
(The instantiation `Params.toSetting / localFun` itself lives in `Zeta23/PrimeSideB/Concrete.lean`.)
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

/-! ## The concrete data satisfy `LocalHyps` -/




end PrimeSide

end Zeta23

end
open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide

theorem solution {P : Params} (hP : P.Valid) : LocalHypsEventually P.crho P := by
  -- l → ∞, L = λ l → ∞, X = e^L ≥ 1
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and hX))
  exact ⟨T₀, fun T hT => localHyps_concrete hP (hT₀ T hT).2.1 (hT₀ T hT).1 (hT₀ T hT).2.2⟩
