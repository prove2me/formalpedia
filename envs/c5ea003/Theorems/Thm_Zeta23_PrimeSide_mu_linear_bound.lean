-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mu_linear_bound
-- name    : Zeta23.PrimeSide.mu_linear_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:00:00.514605+00:00
-- url     : https://prove2.me/theorems/1bc6d4a3-503c-4d98-9b7e-fe58ea0cbfab
-- title:
--   Crude global bound $|\mu(\tau)| \le M + |\tau|$
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], $\mu(\tau)=\tfrac{1}{2\pi}\operatorname{Re}\psi_0(\tfrac14+\tfrac{i\tau}{2})-\tfrac{\log\pi}{2\pi}$. Assume the Stirling-type facts H-$\Gamma$ (`Zeta23.GammaFacts`, [eq:mufacts]).
--
--   Then there exists a constant $M\ge 0$ such that
--   $$|\mu(\tau)|\ \le\ M+|\tau|\qquad\text{for all }\tau\in\mathbb{R}.$$
--   The bound is deliberately crude (the true growth is logarithmic): it is only used to control contributions from increments $|r|>\tau_k/2$, in the spirit of the paper's "$|\mu(\tau_k+r)-\mu(\tau_k)|\ll l+\log(2+|r|)$" (§5.2), where a linear majorant integrated against the rapidly decaying taper weights suffices.
--
--   In module `Zeta23.PrimeSideA.Basic` it feeds the increment bound `mu_increment_bound`, the one-grid-point trace estimate `mu_part_bound`, and the integrability statement `mu_part_integrable` for $\hat\varphi(r)^2\mu(t+r)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L991-L1031, docstring tag [eq:mufacts]

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

theorem Zeta23.PrimeSide.mu_linear_bound (hΓ : Zeta23.GammaFacts) : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, |Zeta23.mu τ| ≤ M + |τ| := by sorry
