-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mu_part_integrable
-- name    : Zeta23.PrimeSide.mu_part_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:00:21.305425+00:00
-- url     : https://prove2.me/theorems/40c07449-b0bc-45e2-9a48-8f501a8d0788
-- title:
--   Integrability of $\hat\varphi(r)^2\,\mu(t+r)$
-- statement:
--   Work in the abstract prime-side setting: taper data $F$ satisfying the core hypotheses `LocalHypsCore`, and let $\mu$ be the archimedean density [eq:mudef]. Assume H-$\Gamma$ (`Zeta23.GammaFacts`).
--
--   Then for every $t>0$ the function
--   $$r\ \longmapsto\ \hat\varphi(r)^2\,\mu(t+r)$$
--   is Lebesgue integrable on $\mathbb{R}$. The proof combines the crude linear bound $|\mu|\le M+|\tau|$ (`mu_linear_bound`) with the moment integrability $\int\hat\varphi^2|r|<\infty$ from [eq:psiints].
--
--   In module `Zeta23.PrimeSideA.Basic` this fact is consumed by `GentryA_diag_eq`, the identification of the diagonal matrix entries $G_{kk}=\int\hat\varphi(\tau-\tau_k)^2\,\nu_X(\tau)\,d\tau$: it justifies splitting off the $\mu$-contribution as a genuine Lebesgue integral in the trace computation [prop:trace].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1248-L1267

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

theorem Zeta23.PrimeSide.mu_part_integrable (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {t : ℝ} (ht0 : 0 < t) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.mu (t + r)) := by sorry
