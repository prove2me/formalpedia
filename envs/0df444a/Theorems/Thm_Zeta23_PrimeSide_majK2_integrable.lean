-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_majK2_integrable
-- name    : Zeta23.PrimeSide.majK2_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:20:34.771669+00:00
-- url     : https://prove2.me/theorems/e2d762a2-c348-4ea2-9beb-c114bf01b741
-- title:
--   Integrability of the $\mathcal{E}_2$ majorant kernel on $\mathbb{R}^2$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $L=\lambda\log(T/2\pi)$, grid points $\tau_k=T+2\pi k/L$ for $0\le k<d$, taper data $F$ with the window-generic core hypotheses (profile constant $c_\varrho$), and majorant $\psi(r)=\min(L,2/|r|,c_\varrho/(wr^2))$. The $\mathcal{E}_2$ majorant kernel is
--   $$K_2(\tau,\tau')\ :=\ L^2\Bigl(\sum_{0\le k<d}\psi(\tau-\tau_k)\,\psi(\tau'-\tau_k)\Bigr)\,|\nu(\tau)|\,|\nu(\tau')|,$$
--   which dominates the integrand $K(\tau,\tau')^2\nu(\tau)\nu(\tau')$ of [eq:trG2int].
--
--   Assume $\nu$ is continuous of level $B\ge 0$ (i.e. $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$) and $T\ge 2\pi$. Then $K_2$ is Lebesgue integrable on $\mathbb{R}^2$ — it is a finite sum of products of integrable one-dimensional weights $\psi(\cdot-\tau_k)\,|\nu|$.
--
--   In module `Zeta23.PrimeSideA.EndsE2` this integrability legitimises the dominated estimates of the off-square error $\mathcal{E}_2=\iint_{\mathbb{R}^2\setminus I\times I}K^2\nu\nu'$; its consumer is the assembly `lem_ends_nu_W`, the core of the end-effects lemma [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE2.lean#L59-L81

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.majK2_integrable (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (_hB0 : 0 ≤ B) (hT : 2 * π ≤ p.T) : Integrable (majK2 cϱ p ν) := by sorry
