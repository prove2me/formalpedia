-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mu_increment_bound
-- name    : Zeta23.PrimeSide.mu_increment_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:22:15.119213+00:00
-- url     : https://prove2.me/theorems/3ef1dd32-4074-4f8e-af7b-5cff137a9a98
-- title:
--   Increment bound $|\mu(t+r)-\mu(t)| \le (K|r| + 10r^2)/t$
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], $\mu(\tau)=\tfrac{1}{2\pi}\operatorname{Re}\psi_0(\tfrac14+\tfrac{i\tau}{2})-\tfrac{\log\pi}{2\pi}$. Assume the Stirling-type facts H-$\Gamma$ (`Zeta23.GammaFacts`), in particular the derivative bound $\mu'(\tau)\ll|\tau|^{-1}$ of [eq:mufacts].
--
--   Then there exists a constant $K\ge 0$ such that for all $t\ge 2$ and every real increment $r$:
--   $$\bigl|\mu(t+r)-\mu(t)\bigr|\ \le\ \frac{K\,|r|+10\,r^2}{t}.$$
--   For small increments ($|r|\le t/2$) this is the mean value theorem with $\mu'\ll 1/\tau$, giving the paper's "$\ll|r|/T$" (§5.2); for large increments the crude linear bound on $\mu$ is absorbed into the $r^2/t$ term using $2|r|/t>1$.
--
--   In module `Zeta23.PrimeSideA.Basic` this quantitative Lipschitz-type estimate is the engine of the local comparisons of $\mu$ against the taper weights: it feeds the diagonal evaluation [prop:mumu] (`prop_mumu`, via `mumu_core`) and the $\mu$-part of the trace estimate [prop:trace] (`prop_trace_mu`, via `mu_part_bound`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1033-L1078, docstring tag [eq:mufacts]

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

theorem Zeta23.PrimeSide.mu_increment_bound (hΓ : Zeta23.GammaFacts) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t := by sorry
