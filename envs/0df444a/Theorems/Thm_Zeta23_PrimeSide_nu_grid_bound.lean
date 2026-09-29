-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_nu_grid_bound
-- name    : Zeta23.PrimeSide.nu_grid_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:17:49.653772+00:00
-- url     : https://prove2.me/theorems/cb59fcf1-9fb6-4429-9110-f79bf1904fdd
-- title:
--   Grid bound N2: $\int_{\tau\notin I}\sigma(\tau)\,|\nu(\tau)|\,d\tau \ll B\,L\,l$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, grid points $\tau_k=T+2\pi k/L$ for $0\le k<d$, window $I=[T,2T]$, taper data $F$ with the window-generic core hypotheses (profile constant $c_\varrho$), and majorant $\psi(r)=\min(L,2/|r|,c_\varrho/(wr^2))$. Set $\sigma(\tau):=\sum_{0\le k<d}\psi(\tau-\tau_k)$, and let the explicit constant be $C_{N2}(c_\varrho):=100\,(1+|\log c_\varrho|+|c_\varrho|)$.
--
--   Assume $\nu$ is continuous of level $B$ (i.e. $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$) in the paper's regime $l\le B$ and $L\le 2l$, and $T\ge 2\pi e^{8}$. Then
--   $$\int_{I^{\,c}}\sigma(\tau)\,|\nu(\tau)|\,d\tau\ \le\ C_{N2}(c_\varrho)\cdot B\,L\,l,$$
--   the integral being over the complement of the window $I$.
--
--   This is estimate N2 of §5.3 ("$\int_{\tau\notin I}|\nu_X|\sigma\ll BLl$"), the polynomial endgame of `nu_grid_bound_raw` in the stated regime (module `Zeta23.PrimeSideA.EndsNu`). Its consumer is `calE2_maj_bound`: combined with the weight bound N1 it controls the off-square error $\mathcal{E}_2$ of the end-effects lemma [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L711-L766

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
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.nu_grid_bound (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBl : p.l ≤ B) (hL2l : p.L ≤ 2 * p.l)
    (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ CN2 cϱ * (B * (p.L * p.l)) := by sorry
