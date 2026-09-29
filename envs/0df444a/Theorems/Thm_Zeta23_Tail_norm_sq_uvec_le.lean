-- Prove2me | Theorems.Thm_Zeta23_Tail_norm_sq_uvec_le
-- name    : Zeta23.Tail.norm_sq_uvec_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:03.171534+00:00
-- url     : https://prove2.me/theorems/8d909d95-dd9c-4a9f-96d3-0e64c31e137f
-- title:
--   $\|u_\rho\|_2^2 \le K^2\, L\cdot \mathrm{dist}(\gamma, I)^{-3}$ for a tail zero
-- statement:
--   **Setup.** Fix a zero configuration $Z$, parameters $P$, and a height $T \ge T_0 = 300$ with $L := P.L\,T \ge 2$. Assume $C_1 \ge 0$ and the decay hypothesis [eq:hfbound] for the taper transform: for all real $r, y$ with $|y| \le 1/2$ and $r - iy \ne 0$,
--   $$\|\hat\varphi_T(r - iy)\| \;\le\; \frac{e^{L/4}\,C_1}{\|r - iy\|^{2}}.$$
--   Let $\rho$ be a zero of the configuration ($\rho \in Z$.carrier) whose ordinate is in the tail: `InTail T ρ.im`, i.e. $\operatorname{Im}\rho \le T - \sqrt T$ or $\operatorname{Im}\rho > 2T + \sqrt T$. The vector $u_\rho \in \mathbb{C}^d$ has entries $u_\rho(k) = \hat\varphi_T(\gamma_\rho - \tau_k)$ at the grid points $\tau_k = T + k\cdot 2\pi/L$, and `distI T γ` is the distance from $\gamma$ to $I = [T, 2T]$.
--
--   **Statement.** With $K := e^{L/4}C_1$,
--   $$\sum_{k<d} \|u_\rho(k)\|^{2} \;\le\; K^{2}\, L\cdot \bigl(\mathrm{distI}\,T\,(\operatorname{Im}\rho)\bigr)^{-3}.$$
--   The proof combines the entrywise decay `norm_uvec_le` ($\|u_\rho(k)\| \le K\,|\gamma_\rho - \tau_k|^{-2}$) with the grid estimate `grid_sum_le` ($\sum_k |\gamma - \tau_k|^{-4} \le L\, D^{-3}$).
--
--   **Role.** This is the per-zero estimate of the tail argument in `Zeta23.Tail`; summed against the multiplicity-weighted zero count `tail_count_sum_le` it yields `TailHyp.partial_sum_le`, hence the norm and trace-norm bounds of Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L229-L261

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
variable (Z : ZeroConfig) (P : Params) (T : ℝ)
variable {P T}
variable {Z}

theorem Zeta23.Tail.norm_sq_uvec_le (hT : T₀ ≤ T) (hL : 2 ≤ P.L T) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
        ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (htail : InTail T ρ.im) :
    ∑ k, ‖uvec P T ρ k‖ ^ 2
      ≤ (Real.exp (P.L T / 4) * C₁) ^ 2 * P.L T * ((distI T ρ.im) ^ 3)⁻¹ := by sorry
