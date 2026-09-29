-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integrable_psiA_shift_mul_nu
-- name    : Zeta23.PrimeSide.integrable_psiA_shift_mul_nu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:18:56.503521+00:00
-- url     : https://prove2.me/theorems/a6be866a-c8f0-405e-a049-6769055dfcca
-- title:
--   Integrability of the shifted majorant $\psi(\cdot-a)\,|\nu|$
-- statement:
--   Work in the abstract prime-side setting of §5: a parameter triple $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, and taper data $F$ satisfying the window-generic core hypotheses (`LocalHypsCoreW`, the taper facts [eq:psidef]–[eq:psiints] etc. with profile constant $c_\varrho\ge 4$ and no cap $\lambda\le 1$). Let $\psi(r)=\min\bigl(L,\ 2/|r|,\ c_\varrho/(w\,r^2)\bigr)$ (with the convention $\psi(0)=L$) be the majorant of [eq:psidef], and let $\nu:\mathbb{R}\to\mathbb{R}$ be a continuous density of level $B$, meaning $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$ for all $\tau$, with $B\ge 1$ and $T\ge 1$.
--
--   Then for every shift $a\in[T,2T]$ the function
--   $$\tau\ \longmapsto\ \psi(\tau-a)\,\bigl|\nu(\tau)\bigr|$$
--   is Lebesgue integrable on $\mathbb{R}$.
--
--   This integrability substrate (module `Zeta23.PrimeSideA.EndsWeighted`) underlies the off-window error term $\mathcal{E}_2$ of the end-effects lemma [lem:ends]: it feeds the integrability of the majorant kernel (`majK2_integrable`), the one-dimensional weight bound N1 (`nu_weight_bound_of_L_le_two_B`), and the estimate of the majorant integral off the square $I\times I$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsWeighted.lean#L154-L199

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

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.integrable_psiA_shift_mul_nu (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F)
    (hν : NuBound p B ν) (hB1 : 1 ≤ B) (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    Integrable (fun τ : ℝ => psiA cϱ p (τ - a) * |ν τ|) := by sorry
