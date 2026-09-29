-- Prove2me | Theorems.Thm_Zeta23_Assembly_err_isLittleO
-- name    : Zeta23.Assembly.err_isLittleO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:32.234938+00:00
-- url     : https://prove2.me/theorems/6bba9531-7544-4770-94e8-ed2897501c03
-- title:
--   The explicit error term in the zero-side lower bound is $o(N)$
-- statement:
--   Step E1 of the assembly: the explicit error accumulated by the lower bound $N_0^*(T,2T) \ge H(\lambda_1) N - \mathrm{err}(T)$ (`N0star_lower_H`) is little-o of the zero count. Let $N, R_1, R_2, N_{I'\setminus I}, B, c_\lambda : \mathbb{R} \to \mathbb{R}$ be real functions of $T$ and $K$ a constant, with: $N(T) \to \infty$; $R_1, R_2, N_{I'\setminus I} = o(N)$ as $T \to \infty$; $B(T) \to 0$; and eventually $0 \le c_\lambda(T) \le K$ (in the application $c_\lambda = 1/\lambda_1 + \lambda_1/3$).
--
--   Then
--   $$4 R_1(T) + R_2(T) + 3 N_{I'\setminus I}(T) + B(T)\left(4 + 2\sqrt{c_\lambda(T)\, N(T) + R_2(T)} + B(T)\right) \;=\; o\big(N(T)\big) \qquad (T \to \infty).$$
--
--   The delicate term is the middle one: $B \sqrt{c_\lambda N + R_2} \ll B\sqrt{N} = o(N)$ precisely because $B \to 0$ and $c_\lambda$ stays bounded. Here $R_1, R_2$ are the explicit remainders of the trace asymptotics [eq:tr1], [eq:tr2], $N_{I'\setminus I}$ the boundary zero count, and $B$ the tail perturbation $\theta_0/(aL)$. Consumed by `thmA_abstract_err` to convert its explicit inequality into the clean $\varepsilon$-form of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L501-L539

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
open Filter Asymptotics Topology

theorem Zeta23.Assembly.err_isLittleO {N R₁ R₂ NII B cl : ℝ → ℝ} {K : ℝ}
    (hN : Tendsto N atTop atTop)
    (hR₁ : R₁ =o[atTop] N) (hR₂ : R₂ =o[atTop] N) (hNII : NII =o[atTop] N)
    (hB : Tendsto B atTop (𝓝 0))
    (hcl : ∀ᶠ T in atTop, 0 ≤ cl T ∧ cl T ≤ K) :
    (fun T => 4 * R₁ T + R₂ T + 3 * NII T
        + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) =o[atTop] N := by sorry
