-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mu_abs_le_l
-- name    : Zeta23.PrimeSide.mu_abs_le_l
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:21:43.335218+00:00
-- url     : https://prove2.me/theorems/e3d19f2c-1f55-41e8-a62c-783ff1310446
-- title:
--   $|\mu(\tau)| \le l$ on the window $I=[T,2T]$ for large $T$
-- statement:
--   Let $\mu$ be the archimedean density of the explicit formula [eq:mudef], $\mu(\tau)=\tfrac{1}{2\pi}\operatorname{Re}\psi_0\bigl(\tfrac14+\tfrac{i\tau}{2}\bigr)-\tfrac{\log\pi}{2\pi}$ ($\psi_0$ the digamma function), and for a setting $p=(T,\lambda,w)$ write $l=\log(T/2\pi)$.
--
--   Assume the Stirling-type facts H-$\Gamma$ for $\mu$ (`Zeta23.GammaFacts`, [eq:mufacts]). Then there exists a threshold $T_0$ such that for every setting $p$ with $T\ge T_0$:
--   $$|\mu(\tau)|\ \le\ l\qquad\text{for all }\tau\in[T,2T].$$
--   This is the two-sided part of the paper's "$0<\mu\le l$ on $I$" (§5.4); only the bound on $|\mu|$ is needed here.
--
--   In module `Zeta23.PrimeSideA.Basic` this sup-bound on the archimedean density over the window is used throughout the evaluation of $\mathcal{M}$: in the cross-term bounds [prop:cross] (i)–(ii) (`prop_cross_muP`, `prop_cross_muPi`), in the diagonal estimate [prop:mumu] (`prop_mumu`), and in the $\mu$-part of the trace estimate (`prop_trace_mu`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L715-L761, docstring tag [eq:mufacts]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.mu_abs_le_l (hΓ : Zeta23.GammaFacts) : ∃ T₀ : ℝ, ∀ p : Setting, T₀ ≤ p.T →
    ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l := by sorry
