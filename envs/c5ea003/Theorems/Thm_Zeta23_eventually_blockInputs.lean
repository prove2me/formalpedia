-- Prove2me | Theorems.Thm_Zeta23_eventually_blockInputs
-- name    : Zeta23.eventually_blockInputs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:56:12.177146+00:00
-- url     : https://prove2.me/theorems/485a2534-c298-4ffe-9625-a19c71d2996c
-- title:
--   The block-decomposition package holds for all large $T$
-- statement:
--   Let $Z$ be an abstract zero configuration and $P = (\varrho, \lambda, w)$ a valid parameter tuple (taper profile $\varrho$, $0 < \lambda \le 1$, $w \ge 1$). The assertion is that for all sufficiently large $T$ (eventually along `atTop`) the package `BlockInputs Z P T` holds. This package records the paper's prop:block together with [eq:Ncount], in both matrix normalizations, for the zero-side matrix $A = A_Z(P,T)$ built from the zeros in $\mathcal{Z}(I')$:
--
--   - **hat units** ($\hat A = A/(aL^2)$): there exist matrices $P_m, Q_m$ and $p \in \mathbb{N}$ with $P_m \succeq 0$, $Q_m$ Hermitian, $\hat A = P_m + Q_m$, $\operatorname{rank} P_m \le s_1 + s_2$, $\operatorname{tr} P_m \le N_{\mathrm{on}}(I')$, $n_+(Q_m) \le p$, and $N_{\mathrm{on}}(I') + 2p \le N(I')$;
--   - **tilde units** ($\tilde A = A/L$): there exist $p$ and a Hermitianity witness with $n_+(\tilde A) \le s_1 + s_2 + p$, $\operatorname{rank} \tilde A \le \#\mathcal{Z}(I')$, and $s_1 + 2s_2 + 2p \le N(I')$.
--
--   Here $s_1, s_2$ count simple and multiple on-line zeros in the window $I' = (T - \sqrt{T},\, 2T + \sqrt{T}]$, $p$ counts off-line pairs, and $n_+$ is the positive index of inertia.
--
--   The theorem (in `Zeta23.Main`) discharges the two analytic inputs of the abstract zero-side result `ZeroSide.eventually_blockInputs_of`: the eventual positivity $a > 0$ (via Taper's $\tfrac12 \le a$, [eq:abdef]) and the Poisson summation identity of [lem:poisson] (`Params.hasSum_phiHatR_sq`). It is consumed by `Zeta23.thmA_lam_of_traces`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Main.lean#L162-L173, docstring tags [prop:block], [eq:Ncount]

import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
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
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Defs_Profile
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Main
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_Taper_Basic
import Definitions.Def_Zeta23_Taper_Params
import Definitions.Def_Zeta23_TracesBoundsE
import Definitions.Def_Zeta23_ZeroSide
import Definitions.Def_Zeta23_ZetaReflect

open Filter Topology
open Zeta23
open Assembly

theorem Zeta23.eventually_blockInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) :
    ∀ᶠ T in atTop, BlockInputs Z P T := by sorry
