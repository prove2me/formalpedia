-- Prove2me | Definitions.Def_Zeta23_PrimeSideA_EndsE2
-- name    : Zeta23_PrimeSideA_EndsE2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:18:20.667525+00:00
-- url     : https://prove2.me/theorems/adae1d45-44d1-4aed-a701-3984071fd42c
-- title:
--   The majorant kernel for the $\mathcal{E}_2$ bound in [lem:ends]
-- statement:
--   This bundle contains the single majorant definition for the bound on $\mathcal{E}_2 := \iint_{(I \times I)^c} K^2\, \nu\, \nu'$ in [lem:ends] (paper §5.3), the off-window contribution to $\operatorname{tr}\tilde G^2$.
--
--   `majK2` is the $\mathcal{E}_2$ majorant kernel with its $\nu$-weights:
--   $$L^2 \Bigl( \sum_{k < d} \psi(\tau - \tau_k)\, \psi(\tau' - \tau_k) \Bigr)\, |\nu(\tau)|\, |\nu(\tau')|,$$
--   where $\psi$ is the taper majorant of [eq:psidef] (`psiA`), $\tau_k = T + kh$ are the grid points, $d$ is the grid size, and $\nu$ is the spectral density. It dominates the integrand $K^2 |\nu||\nu'|$ since $|\hat\varphi| \le \psi$ pointwise, and $|K| \le L \cdot (\text{one } \psi\text{-factor})$.
--
--   Role: integrating `majK2` over the complement of $I \times I$ and factoring each grid term into the two one-dimensional estimates of `Zeta23/PrimeSideA/EndsNu.lean` — N1 ($\int_{\mathbb{R}} \psi(\tau - a)\, |\nu_X(\tau)|\, d\tau \ll B$ uniformly for $a \in I$) and N2 ($\int_{\mathbb{R} \setminus I} |\nu_X|\, \sigma \ll B L l$) — gives the bound $|\mathcal{E}_2| \ll L^2 \cdot B \cdot BLl$, the dominant error in [lem:ends], which feeds the [thm:traces] assembly.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE2.lean

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

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₂ (§5.3).  Statement consumed by
Zeta23/PrimeSideA/Ends.lean.
Substrate: Zeta23/PrimeSideA/EndsWeighted.lean; 1-D estimates N1/N2 from
Zeta23/PrimeSideA/EndsNu.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

section Assembly

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}


/-- the 𝓔₂ majorant kernel with its ν-weights: `L²·(Σ_{k<d} ψ(τ−τ_k)ψ(τ'−τ_k))·|ν(τ)||ν(τ')|`. -/
def majK2 (cϱ : ℝ) (p : Setting) (ν : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  p.L ^ 2 * (∑ k ∈ Finset.range p.d, psiA cϱ p (q.1 - p.tau k) * psiA cϱ p (q.2 - p.tau k))
    * (|ν q.1| * |ν q.2|)





end Assembly

section Bounds
variable (cϱ lam : ℝ)






end Bounds

end PrimeSide
end Zeta23


