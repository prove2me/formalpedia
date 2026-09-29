-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_eventually_blockInputs_of
-- name    : Zeta23.ZeroSide.eventually_blockInputs_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:55:22.374907+00:00
-- url     : https://prove2.me/theorems/792c9167-dd35-4bcf-a867-249cd0ac822f
-- title:
--   Block inputs hold for all sufficiently large $T$
-- statement:
--   Let $Z$ be a zero configuration and $P$ a parameter choice satisfying `P.Valid` (a genuine taper profile $\varrho$, exponent $0 < \lambda \le 1$, ramp width $w \ge 1$). Assume, in the filter sense 'for all sufficiently large $T$':
--   - (ha) the normalisation $a(T) = L^{-1} \int \varphi^2$ is positive, and
--   - (hPois) the Poisson identity `PoissonSq T P` holds: $\sum_{k \in \mathbb{Z}} \hat\varphi(\gamma - \tau_k)^2 = a L^2$ for every real $\gamma$ ([lem:poisson]).
--
--   **Statement.** Then for all sufficiently large $T$, `Assembly.BlockInputs Z P T` holds — the full package of prop:block (i)+(ii) and [eq:Ncount] at height $T$ (decomposition $\hat A = P + Q$ with rank, trace and positive-index bounds, and the counting inequalities relating $s_1, s_2, p$ to $N(I')$).
--
--   The remaining hypotheses of `blockInputsAt` are discharged internally: the conjugation and realness properties of $\hat\varphi$ follow from $\varphi$ being real and even, and $L(T) = \lambda \log(T/2\pi) \to \infty$ gives $0 < L$ and $0 < a L^2$ eventually.
--
--   **Role.** This is the export of the module `Zeta23.ZeroSide` consumed by `Zeta23.eventually_blockInputs` in Main.lean: only the genuinely external inputs (positivity of $a$ and lem:poisson, both discharged in `Zeta23/ZeroSide/Final.lean`) are left as hypotheses on the route to Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L985-L992, docstring tags [prop:block], [eq:Ncount]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide

set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
open Zeta23

theorem Zeta23.ZeroSide.eventually_blockInputs_of (Z : ZeroConfig) (P : Params) (hP : P.Valid)
    (ha : ∀ᶠ T in Filter.atTop, 0 < P.a T) (hPois : ∀ᶠ T in Filter.atTop, PoissonSq T P) :
    ∀ᶠ T in Filter.atTop, Assembly.BlockInputs Z P T := by sorry
