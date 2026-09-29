-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_nu_weight_bound_of_L_le_two_B
-- name    : Zeta23.PrimeSide.nu_weight_bound_of_L_le_two_B
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:19:29.847123+00:00
-- url     : https://prove2.me/theorems/7ee32b42-f69a-446b-944c-a62043cfe8fe
-- title:
--   Weight bound N1, master form: $\int_{\mathbb{R}}\psi(\tau-a)\,|\nu(\tau)|\,d\tau \ll \Psi_0 B$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $L=\lambda\log(T/2\pi)$, taper data $F$ with the window-generic core hypotheses (profile constant $c_\varrho$), and majorant $\psi(r)=\min(L,2/|r|,c_\varrho/(wr^2))$.
--
--   Assume $\nu$ is continuous of level $B$ (i.e. $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$) with $L\le 2B$ and $B\ge 4$, and $T\ge 1$. Then for every shift $a\in[T,2T]$:
--   $$\int_{\mathbb{R}}\psi(\tau-a)\,|\nu(\tau)|\,d\tau\ \le\ \Bigl(2\bigl(4+2\log\tfrac{c_\varrho L}{4w}\bigr)+7c_\varrho\Bigr)\,B.$$
--   The leading factor is $2\Psi_0+7c_\varrho$ with $\Psi_0=4+2\log(c_\varrho L/4w)$ the half-line integral of $\psi$ [eq:psiints]; this is the paper's "the second factor is $\le 3\Psi_0 B$ uniformly in $k$" (§5.3) in master form.
--
--   The two paper regimes are corollaries: `nu_weight_bound` (for $B\ge l\ge L/2$) and `nu_weight_bound_L` (for $B\ge L$). In module `Zeta23.PrimeSideA.EndsNu` it is consumed by `calE2_maj_bound`: it bounds the full-line factor $\int_{\mathbb{R}}\psi_k|\nu|$ in the estimate $|\mathcal{E}_2|\le 2L^2\sum_k(\int_{I^c}\psi_k|\nu|)(\int_{\mathbb{R}}\psi_k|\nu|)$ for the end-effects lemma [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L99-L184

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

theorem Zeta23.PrimeSide.nu_weight_bound_of_L_le_two_B (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hL2B : p.L ≤ 2 * B) (hB4 : 4 ≤ B)
    (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B := by sorry
