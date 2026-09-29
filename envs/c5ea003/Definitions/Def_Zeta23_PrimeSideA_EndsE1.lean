-- Prove2me | Definitions.Def_Zeta23_PrimeSideA_EndsE1
-- name    : Zeta23_PrimeSideA_EndsE1
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:16:39.742294+00:00
-- url     : https://prove2.me/theorems/287ea5a5-d043-4a08-a66f-e2638c77496c
-- title:
--   Boundary weight $g$, tail functional $W$, and the majorant kernel for the $\mathcal{E}_1$ bound
-- statement:
--   This bundle provides the weights and majorants used to bound $\mathcal{E}_1 := \iint_{I \times I}(K^2 - K_\infty^2)\,\nu\,\nu'$ in [lem:ends] (paper §5.3), on the window $I = [T, 2T]$.
--
--   The members: `distB` is the distance to the boundary of $I$, $\min(\tau - T,\ 2T - \tau)$ (for $\tau \in I$); `gwt` is the weight $g(\tau) := \bigl(1 + \min(\tau - T,\ 2T - \tau)\bigr)^{-2}$, which lies in $(0, 1]$ on $I$; `Wfun` is the tail functional
--   $$W(\Delta) \;:=\; \psi(\Delta)^2 + h^{-1} \int_{(\Delta, \infty)} \psi^2,$$
--   with $\psi$ the majorant of [eq:psidef] and $h = 2\pi/L$ the grid spacing; and `majK1` is the $\mathcal{E}_1$ majorant kernel with its $\nu$-weights on $I \times I$:
--   $$L^2 \Bigl( \frac{\rho(\tau)}{g(\tau)}\, g(\tau') + g(\tau)\, \frac{\rho(\tau')}{g(\tau')} \Bigr) |\nu(\tau)|\, |\nu(\tau')|.$$
--
--   Role: the pointwise weighted AM–GM bound $|K_\infty - K| \le \tfrac12(s\,\rho(\tau) + \rho(\tau')/s)$ with $s := g(\tau')/g(\tau)$, together with $|K + K_\infty| \le 2L^2$, dominates the $\mathcal{E}_1$ integrand by `majK1`; the product structure then gives $|\mathcal{E}_1| \le 2 L^2 B^2 (\int_I \rho/g)(\int_I g)$ with $\int_I g \le 2$ and $\int_I \rho/g \ll L^2 + L\,l$ (via the majorant $\rho(\tau) \le W(\tau - T) + W(2T - \tau) + \psi(\tau_d - \tau)^2$), yielding the bound `calE1_bound` consumed by the [lem:ends] assembly.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean

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

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₁ (§5.3).  Statement `calE1_bound` consumed by
Zeta23/PrimeSideA/Ends.lean.

ROUTE.  On I×I: |ν|,|ν'| ≤ B;  |K + K_∞| ≤ 2L² (abs_Kfun_le, abs_Kinf_le);
|K_∞ − K| ≤ (s ρ(τ) + ρ(τ')/s)/2 for every s > 0 (abs_Kinf_sub_Kfun_le), with the choice
s := g(τ')/g(τ), g(τ) := (1 + min(τ−T, 2T−τ))⁻² > 0.  Hence pointwise
  |K²−K_∞²||ν||ν'| ≤ L²B² ( ρ(τ)/g(τ)·g(τ') + g(τ)·ρ(τ')/g(τ') )
and integrating over I×I (product structure):  |𝓔₁| ≤ 2L²B² (∫_I ρ/g)(∫_I g),  ∫_I g ≤ 2.
Pointwise majorant (finite partial sums of the HasSum for ρ, ψ antitone, grid lemma):
  ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d − τ)²,   W(Δ) := ψ(Δ)² + h⁻¹∫_{(Δ,∞)}ψ²,
and 1/g = (1+min(τ−T,2T−τ))² ≤ (1+(τ−T))², (1+(2T−τ))², (1+h+|τ_d−τ|)² respectively, so
  ∫_I ρ/g ≤ 2∫_0^T W(u)(1+u)² du + ∫_ℝ ψ(r)²(2+|r|)² dr ≪ L² + L·l   (split at 1; ψ ≤ L,
  ψ(r) ≤ (c/w)/r², ∫_{(Δ,∞)}ψ² ≤ min(8L, (c/w)²/(3Δ³)), log T ≤ 2l).
Budget: |𝓔₁| ≤ C(c_ϱ)·L²B²(L² + L l) ≤ C·L³B² l (L = λl ≤ l).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-! ### Definitions -/

/-- `W(Δ) := ψ(Δ)² + h⁻¹ ∫_{(Δ,∞)} ψ²`. -/
def Wfun (cϱ : ℝ) (p : Setting) (Δ : ℝ) : ℝ :=
  psiA cϱ p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2

/-- distance to the boundary of `I = [T,2T]` (for τ ∈ I): `min(τ−T, 2T−τ)`. -/
def distB (p : Setting) (τ : ℝ) : ℝ := min (τ - p.T) (2 * p.T - τ)

/-- the weight `g(τ) := (1 + min(τ−T,2T−τ))⁻²` (only used for τ ∈ I, where it is in (0,1]). -/
def gwt (p : Setting) (τ : ℝ) : ℝ := ((1 + distB p τ) ^ 2)⁻¹

/-! ### Leaf integrals -/










/-! ### Pointwise facts on I -/




/-- the 𝓔₁ majorant kernel with its ν-weights (on `I×I`):
`L²·(ρ(τ)/g(τ)·g(τ') + g(τ)·ρ(τ')/g(τ'))·|ν(τ)||ν(τ')|`,  g = gwt. -/
def majK1 (p : Setting) (F : LocalFun) (ν : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  p.L ^ 2 * (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
    * (|ν q.1| * |ν q.2|)




/-! ### The majorant for ρ on I -/






/-! ### The weight integrals -/



/-! ### Assembly -/

section Bounds
variable (cϱ lam : ℝ)




end Bounds

section BoundsCor
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}


variable (cϱ lam : ℝ)


end BoundsCor

end PrimeSide
end Zeta23


