-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integral_psiA_mul_sqrt_le
-- name    : Zeta23.PrimeSide.integral_psiA_mul_sqrt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:19:13.475744+00:00
-- url     : https://prove2.me/theorems/9c3e5581-1ffd-48af-8a46-0479c5b4b514
-- title:
--   Weighted majorant integral: $\int_{\mathbb{R}}\psi(r)\sqrt{|r|}\,dr \le 2L + 4c_\varrho/w$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $L=\lambda\log(T/2\pi)$, taper data $F$ satisfying the window-generic core hypotheses with profile constant $c_\varrho$, and majorant $\psi(r)=\min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ (with $\psi(0)=L$).
--
--   Then
--   $$\int_{\mathbb{R}}\psi(r)\,\sqrt{|r|}\;dr\ \le\ 2L\ +\ \frac{4\,c_\varrho}{w}.$$
--   The proof splits the range: $\psi\le L$ on $|r|\le 1$, and $\psi(r)\sqrt{r}\le (c_\varrho/w)\,r^{-3/2}$ for $r>1$.
--
--   In the project (module `Zeta23.PrimeSideA.EndsNu`) this square-root moment of the majorant enters the master weight bound N1 (`nu_weight_bound_of_L_le_two_B`, §5.3), where it absorbs the $\log^+$ tail growth $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$ of the density via $\log^+ x\le 2\sqrt{x}$, on the way to the $\mathcal{E}_2$ estimate of the end-effects lemma [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L46-L97

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

theorem Zeta23.PrimeSide.integral_psiA_mul_sqrt_le (hF : LocalHypsCoreW cϱ p F) :
    ∫ r, psiA cϱ p r * Real.sqrt |r| ≤ 2 * p.L + 4 * (cϱ / p.w) := by sorry
