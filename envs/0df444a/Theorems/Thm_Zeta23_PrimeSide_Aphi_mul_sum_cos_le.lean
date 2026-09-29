-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Aphi_mul_sum_cos_le
-- name    : Zeta23.PrimeSide.Aphi_mul_sum_cos_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:59:17.535605+00:00
-- url     : https://prove2.me/theorems/d5e5d3a3-5803-4dbb-b039-4b733a0c3a80
-- title:
--   Dirichlet-kernel bound for $A_\varphi(y)\,\bigl|\sum_{k<d}\cos(\tau_k y)\bigr|$
-- statement:
--   Let $p$ be a parameter setting with height $T$, window length $L$, grid spacing $h = 2\pi/L$, grid size $d = \lfloor LT/2\pi\rfloor$ and grid points $\tau_k = T + kh$, and let $F$ be a taper datum whose autocorrelation $A_\varphi = \varphi \star \varphi$ satisfies the window-generic hypotheses `LocalHypsCore` (in particular $0 \le A_\varphi(y) \le (L - |y|)_+$, from [eq:gbounds]).
--
--   Then for every real $y \ge \log 2$,
--   $$\Bigl|\,A_\varphi(y)\sum_{k=0}^{d-1}\cos(\tau_k y)\,\Bigr| \;\le\; \frac{L^2}{2\log 2}.$$
--   This is the pointwise $P$-part bound of [prop:trace] (§5.2): the cosine sum is a Dirichlet kernel bounded by $1/|\sin(hy/2)|$, which Jordan's inequality controls, while $A_\varphi(y) \le (L-y)_+$ vanishes for $y \ge L$.
--
--   In the project this feeds `sum_P_part_bound`, which sums the prime-power contributions $G^P_{kk}$ over the grid in the trace asymptotics for the prime-side Gram matrix (module `Zeta23.PrimeSideA.Basic`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L821-L875, docstring tags [prop:trace], [eq:gbounds]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.Aphi_mul_sum_cos_le (hF : LocalHypsCore cϱ p F) {y : ℝ} (hy : Real.log 2 ≤ y) :
    |F.Aphi y * ∑ k ∈ Finset.range p.d, Real.cos (p.tau k * y)| ≤ p.L ^ 2 / (2 * Real.log 2) := by sorry
