-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integrable_psiA_mul_sqrt
-- name    : Zeta23.PrimeSide.integrable_psiA_mul_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:18:05.822884+00:00
-- url     : https://prove2.me/theorems/e6bb822e-e570-4e1c-b04d-ce8e9f7499b2
-- title:
--   Integrability of $\psi(r)\sqrt{|r|}$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. Here $\psi(r) = \min\bigl(L,\, 2/|r|,\, c_\varrho/(w r^2)\bigr)$ (with the convention $\psi(0) = L$) is the taper majorant of [eq:psidef], dominating both $|\hat\varphi|$ and $|\Phi|$. Assuming the taper facts `LocalHypsCoreW`, the theorem asserts that the function
--   $$r \;\longmapsto\; \psi(r)\, \sqrt{|r|}$$
--   is Lebesgue integrable on $\mathbb{R}$: near $r = 0$ the integrand is at most $L\sqrt{|r|}$, and at infinity the $c_\varrho/(w r^2)$ regime gives decay of order $|r|^{-3/2}$, both integrable.
--
--   The $\sqrt{|r|}$ weight is exactly what the $\log^+$ growth of the density bound `NuBound` costs after the absorption $\log^+ x \le 2\sqrt{x}$; the lemma is the integrability substrate for the $\psi$-weighted $\nu$ integrals of the ends analysis, consumed by `integrable_psiA_shift_mul_nu`, `integral_psiA_mul_sqrt_le` and `nu_weight_bound_of_L_le_two_B` in the proof of [lem:ends] (module `Zeta23.PrimeSideA.EndsWeighted`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsWeighted.lean#L99-L152

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
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}
set_option maxHeartbeats 1000000

theorem Zeta23.PrimeSide.integrable_psiA_mul_sqrt (hF : LocalHypsCoreW cϱ p F) :
    Integrable (fun r : ℝ => psiA cϱ p r * Real.sqrt |r|) := by sorry
