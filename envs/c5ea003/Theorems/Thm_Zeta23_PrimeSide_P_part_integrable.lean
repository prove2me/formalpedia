-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_P_part_integrable
-- name    : Zeta23.PrimeSide.P_part_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:59:46.471358+00:00
-- url     : https://prove2.me/theorems/03c1f42d-a000-429d-a968-ab6e6209b92d
-- title:
--   Integrability of $r \mapsto \hat\varphi(r)^2\,P_X(t+r)$
-- statement:
--   Let $p$ be a parameter setting with prime cutoff $X$ and $F$ a taper datum satisfying the window-generic package `LocalHypsCore` (in particular $\hat\varphi^2$ is integrable), and recall that $P_X$ [eq:Pdef] is a finite cosine sum, hence continuous and bounded.
--
--   The theorem asserts that for every real $t$ the function
--   $$r \;\longmapsto\; \hat\varphi(r)^2\,P_X(t+r)$$
--   is integrable on $\mathbb R$ — a bounded continuous factor times an integrable one.
--
--   This justifies splitting the diagonal Gram entry $G_{kk} = \int\hat\varphi(r)^2\,\nu_X(\tau_k+r)\,dr$ into its $\mu$-, $\Pi$- and $P$-parts in `GentryA_diag_eq` (module `Zeta23.PrimeSideA.Basic`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1233-L1246

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

theorem Zeta23.PrimeSide.P_part_integrable (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)) := by sorry
