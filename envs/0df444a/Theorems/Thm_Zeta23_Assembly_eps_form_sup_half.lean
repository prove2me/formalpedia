-- Prove2me | Theorems.Thm_Zeta23_Assembly_eps_form_sup_half
-- name    : Zeta23.Assembly.eps_form_sup_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:11.563921+00:00
-- url     : https://prove2.me/theorems/eabc7a42-40b1-4715-b369-c1eb841e32d5
-- title:
--   Passing to the supremum of the constant in the $\varepsilon$-form
-- statement:
--   An abstract lemma formalizing the common "$\lambda \to 1^-$" step. Let $c : \mathbb{R} \to \mathbb{R}$ assign a constant to each parameter value $\lambda$, let $C$ be a target constant, and let $N, \mathrm{lower} : \mathbb{R} \to \mathbb{R}$ with $N(T) \ge 0$ for all $T$. Say the *$\varepsilon$-form holds with constant $\kappa$* if for every $\varepsilon > 0$ there is $T_0$ with $(\kappa - \varepsilon) N(T) \le \mathrm{lower}(T)$ for all $T \ge T_0$.
--
--   Assume: (i) $C$ is approached from below, i.e. for every $\eta > 0$ there exists $\lambda \in [1/2, 1)$ with $C - \eta \le c(\lambda)$; and (ii) for every $\lambda \in [1/2, 1)$ the $\varepsilon$-form holds with constant $c(\lambda)$. Then the $\varepsilon$-form holds with constant $C$:
--   $$\forall \varepsilon > 0,\ \exists T_0,\ \forall T \ge T_0: \quad (C - \varepsilon)\, N(T) \;\le\; \mathrm{lower}(T).$$
--
--   Given $\varepsilon$, one picks $\lambda$ with $c(\lambda) \ge C - \varepsilon/2$ and applies the hypothesis at $(\lambda, \varepsilon/2)$; nonnegativity of $N$ makes the constants compose. In the project this feeds `eps_form_twoThirds`, where $c = H$ and $C = 2/3 = \sup_{\lambda < 1} H(\lambda)$, in the `Zeta23.Assembly` module.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L541-L552

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

theorem Zeta23.Assembly.eps_form_sup_half {c : ℝ → ℝ} {C : ℝ}
    (hc : ∀ η > (0:ℝ), ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧ C - η ≤ c lam)
    {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (C - ε) * N T ≤ lower T := by sorry
