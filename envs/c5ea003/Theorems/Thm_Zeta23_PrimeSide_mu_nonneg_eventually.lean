-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mu_nonneg_eventually
-- name    : Zeta23.PrimeSide.mu_nonneg_eventually
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:25:57.275642+00:00
-- url     : https://prove2.me/theorems/859803f6-1198-44ad-a977-edfad6116dfa
-- title:
--   Eventual nonnegativity of the archimedean density $\mu$
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], $\mu(\tau)=\tfrac{1}{2\pi}\operatorname{Re}\psi_0(\tfrac14+\tfrac{i\tau}{2})-\tfrac{\log\pi}{2\pi}$, where $\psi_0$ is the digamma function. Assume the Stirling-type facts H-$\Gamma$ (`Zeta23.GammaFacts`).
--
--   Then there exists $\tau_0\ge 0$ such that
--   $$\mu(x)\ \ge\ 0\qquad\text{for all }x\ge\tau_0.$$
--   Since by H-$\Gamma$ one has $\mu(\tau)=\tfrac{1}{2\pi}\log(|\tau|/2\pi)+O(\tau^{-2})$ (Stirling), $\mu$ is eventually positive; this renders the paper's "$\mu$ is positive … on $[T-h,2T]$" (§5.2) in a threshold form.
--
--   In module `Zeta23.PrimeSideA.Basic` this positivity is consumed by `prop_trace_mu`, the $\mu$-part of the trace estimate [prop:trace], where the sign of $\mu$ near the window matters in the Riemann-sum comparison of $\sum_k\mu(\tau_k)$ against $\int_I\mu$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1294-L1315

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

theorem Zeta23.PrimeSide.mu_nonneg_eventually (hΓ : Zeta23.GammaFacts) :
    ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ∀ x, τ₀ ≤ x → 0 ≤ Zeta23.mu x := by sorry
