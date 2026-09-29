-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_lem_ends_nu_W
-- name    : Zeta23.PrimeSide.lem_ends_nu_W
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:21:28.240724+00:00
-- url     : https://prove2.me/theorems/ead00a58-ef8f-407c-a7cb-b1ff090e06e5
-- title:
--   End effects, $\nu$-generic window-generic core of [lem:ends]
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, grid points $\tau_k=T+2\pi k/L$, $d=\lfloor LT/2\pi\rfloor$, and taper data $F$. For an abstract density $\nu:\mathbb{R}\to\mathbb{R}$ the matrix entries are $G_{kl}(\nu)=\int_{\mathbb{R}}\hat\varphi(\tau-\tau_k)\hat\varphi(\tau-\tau_l)\,\nu(\tau)\,d\tau$, and $\mathcal{M}(\nu)=\iint_{I\times I}\Phi(\tau-\tau')^2\nu(\tau)\nu(\tau')\,d\tau\,d\tau'$ with $I=[T,2T]$.
--
--   Fix a bandwidth ratio $\lambda>0$ and profile constant $c_\varrho$. Then there exist $C$ and $T_0$ such that for every setting $p$ with $p.\lambda=\lambda$ and $T\ge T_0$, every taper $F$ satisfying the window-generic core hypotheses `LocalHypsCoreW` (no cap $\lambda\le 1$) together with $L\le 2l$, and every continuous $\nu$ of level $B$ (i.e. $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$) with $l\le B$:
--   $$\Bigl|L^{-2}\sum_{0\le k,l<d}G_{kl}(\nu)^2\ -\ \mathcal{M}(\nu)\Bigr|\ \le\ C\,L\,l\,\log l\;B^2.$$
--
--   This is the common core of [lem:ends] (§5.3), proved by splitting the error into $\mathcal{E}_1$ (inside $I\times I$, Poisson-tail term) and $\mathcal{E}_2$ (off the square). The window-generic hypotheses and the cap $L\le 2l$ make it usable downstream with $\lambda\in(1,2]$ (the family regime of Theorem E); in this project it directly yields `lem_ends`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Ends.lean#L63-L109, docstring tag [lem:ends]

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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
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

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.lem_ends_nu_W :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      |(p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 - MtotalNu ν p F|
        ≤ C * (p.L * p.l * Real.log p.l * B ^ 2) := by sorry
