-- Prove2me | Theorems.Thm_Zeta23_GzGp_phiHat_conj
-- name    : Zeta23.GzGp.phiHat_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:40.203908+00:00
-- url     : https://prove2.me/theorems/fb873ec2-961f-4434-8645-77d8fb0dafbd
-- title:
--   Conjugation symmetry of the taper transform: $\hat\varphi(\bar z) = \overline{\hat\varphi(z)}$
-- statement:
--   Let $\varphi$ be the taper of the test family (a real-valued even function; here $\varphi(u) = \varrho((L/2-|u|)/w)$ for the parameter pack $P$ at height $T$) and let $\hat\varphi(z) = \int_{\mathbb{R}} \varphi(u)\,e^{izu}\,du$ be its paper Fourier transform, defined for all complex $z$. Then for every $z \in \mathbb{C}$,
--
--   $$\hat\varphi(\bar z) \;=\; \overline{\hat\varphi(z)}.$$
--
--   In particular $\hat\varphi$ is real on the real axis. The proof uses only that $\varphi$ is real-valued and even (the paper's remark after [eq:fk]: since $\hat\varphi$ is real on $\mathbb{R}$ we have $\overline{\hat\varphi(\bar z)} = \hat\varphi(z)$).
--
--   **Role.** This symmetry is used throughout the H-EF bridge and the zero side: in `GzGp.EFrhs_eq_Gp` and `ZeroConfig.Gz_eq_Gp` (matching the conjugations in [eq:Wdef] with [eq:Gdef]), in the tail estimates (`Tail.eventually_tailPackage`), and in assembling the zero-side block inputs (`ZeroSide.eventually_blockInputs_of`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Hypotheses/GzGp.lean#L55-L70

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs

open scoped ComplexConjugate
open Complex MeasureTheory Set
open Zeta23
variable (P : Params) (T : ℝ)

theorem Zeta23.GzGp.phiHat_conj (z : ℂ) : P.phiHat T (conj z) = conj (P.phiHat T z) := by sorry
