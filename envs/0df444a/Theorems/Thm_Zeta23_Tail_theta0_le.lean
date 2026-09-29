-- Prove2me | Theorems.Thm_Zeta23_Tail_theta0_le
-- name    : Zeta23.Tail.theta0_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:46:53.03741+00:00
-- url     : https://prove2.me/theorems/387599c2-3ad7-48d5-8eb6-81b38609f113
-- title:
--   Size of $\theta_0$: $\theta_0 \le 32\,A_0\,\|\varrho''\|_1^2\, \ell\, T^{\lambda/2 - 1}$
-- statement:
--   **Setup.** Here $\theta_0(A_0, K, T) := 4A_0K^2\log(4T)/T$ is the tail bound of Proposition [prop:tail], evaluated at $K = e^{L/4}C_1$, with $L = P.L\,T = \lambda\,\ell(T)$ the concrete logarithmic length of `Defs.lean` ($\ell(T) = \log(T/2\pi)$, and $e^{L/2} = X^{1/2} = (T/2\pi)^{\lambda/2}$). Assume: valid parameters $P$ (so $0 < \lambda \le 1$), $T \ge T_0 := 300$, $A_0 \ge 0$, $C_1 \ge 0$, and $C_1 \le 2R$ — in the application $R = \|\varrho''\|_1$ and $C_1 = \|\varphi''\|_1 = 2\|\varrho''\|_1/w \le 2\|\varrho''\|_1$ since the ramp width satisfies $w \ge 1$.
--
--   **Statement.**
--   $$\theta_0\!\bigl(A_0,\ e^{L/4}C_1,\ T\bigr) \;\le\; 32\,A_0\,R^{2}\,\ell(T)\; T^{\lambda/2 - 1}.$$
--   This is the "so that" clause of [prop:tail]: it combines $e^{L/2} = (T/2\pi)^{\lambda/2} \le T^{\lambda/2}$, $C_1^2 \le 4R^2$, $\log(4T) \le 2\ell(T)$ (`log_four_mul_le_two_mul_l`), and $D_0^2 = T$. Since $\lambda \le 1$, the right-hand side is $\ll \ell\,T^{\lambda/2-1} \to 0$, so the tail contribution is asymptotically negligible.
--
--   **Role.** Consumed by `eventually_tailPackage` in `Zeta23.Tail`, which exports [prop:tail] to `Main.lean` together with exactly this decay bound on $\theta_0$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L79-L112, docstring tag [prop:tail]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg

theorem Zeta23.Tail.theta0_le (P : Params) (hP : P.Valid) {T A₀ C₁ R : ℝ} (hT : T₀ ≤ T) (hA₀ : 0 ≤ A₀)
    (hC₁ : 0 ≤ C₁) (hC₁R : C₁ ≤ 2 * R) :
    theta0 A₀ (Real.exp (P.L T / 4) * C₁) T ≤ 32 * A₀ * R ^ 2 * l T * T ^ (P.lam / 2 - 1) := by sorry
