-- Prove2me | Theorems.Thm_Zeta23_Assembly_isLittleO_sqrtX_Tl
-- name    : Zeta23.Assembly.isLittleO_sqrtX_Tl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:42:24.751276+00:00
-- url     : https://prove2.me/theorems/6e6c4de1-7cc2-4935-b0cb-3e1075c3a4b5
-- title:
--   $\sqrt{X} = (T/2\pi)^{\lambda/2} = o(T\,l)$
-- statement:
--   For a fixed parameter pack $P$ with exponent $\lambda = $ `P.lam`, write $l = l(T) := \log(T/2\pi)$, $L := \lambda l$, and $X = X(T) := e^L = (T/2\pi)^\lambda$ (the mollifier length). Assume $0 < \lambda \le 1$.
--
--   Then
--   $$\sqrt{X(T)} \;=\; (T/2\pi)^{\lambda/2} \;=\; o\big(T\, l(T)\big) \qquad (T \to \infty)$$
--   in the sense of `Asymptotics.IsLittleO` along the filter at infinity. (The exponent $\lambda/2 \le 1/2 < 1$ is what matters; the statement holds for any $\lambda < 2$.)
--
--   In the assembly of Theorem A, $L\sqrt{X}$ is the error of the first trace asymptotic [eq:tr1], while the zero count satisfies $N(T,2T) \gg T l$; this little-o estimate shows that trace error is $o(N)$, one of the inputs to `err_isLittleO` inside `thmA_abstract_err`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L814-L831

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_TracesBoundsE

open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open Filter Asymptotics Topology Real

theorem Zeta23.Assembly.isLittleO_sqrtX_Tl (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) :
    (fun T => Real.sqrt (P.X T)) =o[atTop] fun T => T * l T := by sorry
