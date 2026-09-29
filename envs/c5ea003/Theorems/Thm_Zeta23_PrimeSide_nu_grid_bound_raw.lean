-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_nu_grid_bound_raw
-- name    : Zeta23.PrimeSide.nu_grid_bound_raw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:17:33.101923+00:00
-- url     : https://prove2.me/theorems/8842386b-976a-4e2c-8553-6d64a2411c40
-- title:
--   Grid bound N2, raw form: the majorant integrated over both half-lines
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, grid points $\tau_k=T+2\pi k/L$ for $0\le k<d$, window $I=[T,2T]$, taper data $F$ with the window-generic core hypotheses (profile constant $c_\varrho$), majorant $\psi(r)=\min(L,2/|r|,c_\varrho/(wr^2))$, and $\sigma(\tau):=\sum_{0\le k<d}\psi(\tau-\tau_k)$.
--
--   Assume $\nu$ is continuous of level $B$ (i.e. $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$) with $B\ge 8$, and $T\ge 2\pi e^{8}$. Then
--   $$\int_{I^{\,c}}\sigma(\tau)\,|\nu(\tau)|\,d\tau\ \le\ 2\Bigl(B\bigl(2+2L+\tfrac{25}{2}c_\varrho L+\tfrac{c_\varrho L^2}{2}+c_\varrho L\,l\bigr)+L\,c_\varrho B\Bigr).$$
--
--   This is the common core of the two regime-specific corollaries `nu_grid_bound` ($B\ge l$, $L\le 2l$) and `nu_grid_bound_L` ($B\ge L$): the distance of $\tau$ to the window is majorised on the near range $(0,2T]$ by `integral_Mnear_le` and on the far range $(2T,\infty)$ by `integral_Mfar_le`, before any polynomial simplification. It lives in module `Zeta23.PrimeSideA.EndsNu` and belongs to estimate N2 of §5.3, feeding the $\mathcal{E}_2$ bound of the end-effects lemma [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L615-L709

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

theorem Zeta23.PrimeSide.nu_grid_bound_raw (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB8 : 8 ≤ B) (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + p.L * cϱ * B) := by sorry
