-- Prove2me | Theorems.Thm_Zeta23_Assembly_eps_form_twoThirds
-- name    : Zeta23.Assembly.eps_form_twoThirds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:25.165712+00:00
-- url     : https://prove2.me/theorems/d8736f07-c3f5-4572-9a5c-68adac6ba6d2
-- title:
--   The $\lambda \to 1^-$ step: from constant $H(\lambda)$ to constant $2/3$
-- statement:
--   Step E3 of the assembly of Theorem A. Let $H(\lambda) := 2 - 1/\lambda - \lambda/3$, so that $H$ is increasing on $(0,1]$ with $\sup_{1/2 \le \lambda < 1} H(\lambda) = H(1) = 2/3$. Let $N, \mathrm{lower} : \mathbb{R} \to \mathbb{R}$ with $N(T) \ge 0$ for all $T$ (in the application, $N(T) = N(T,2T)$ is the zero count and $\mathrm{lower}(T) = N_0^*(T,2T)$).
--
--   Assume that for every $\lambda \in [1/2, 1)$ the $\varepsilon$-form holds with constant $H(\lambda)$: for every $\varepsilon > 0$ there is $T_0$ with $(H(\lambda) - \varepsilon) N(T) \le \mathrm{lower}(T)$ for all $T \ge T_0$. Then the $\varepsilon$-form holds with constant $2/3$:
--   $$\forall \varepsilon > 0,\ \exists T_0,\ \forall T \ge T_0: \quad \left(\tfrac{2}{3} - \varepsilon\right) N(T) \;\le\; \mathrm{lower}(T).$$
--
--   This is the specialization of `eps_form_sup_half` to $c = H$, $C = 2/3$, using continuity of $H$ at $1$. It is the last analytic step turning "Theorem A at each fixed $\lambda < 1$" into the headline constant $2/3$; it is consumed by `Zeta23.thmA_of_lam`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L559-L567

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

theorem Zeta23.Assembly.eps_form_twoThirds {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (Hfun lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2 / 3 - ε) * N T ≤ lower T := by sorry
