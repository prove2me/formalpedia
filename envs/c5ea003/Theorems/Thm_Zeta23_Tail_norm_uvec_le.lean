-- Prove2me | Theorems.Thm_Zeta23_Tail_norm_uvec_le
-- name    : Zeta23.Tail.norm_uvec_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:57.471142+00:00
-- url     : https://prove2.me/theorems/00a43c21-e7cd-4a68-bffd-65e1c2096288
-- title:
--   Entrywise decay of $u_\rho$: $\|u_\rho(k)\| \le e^{L/4}C_1\,|\gamma_\rho - \tau_k|^{-2}$
-- statement:
--   **Setup.** Fix a zero configuration $Z$, parameters $P$, a height $T > 0$ with $L := P.L\,T > 0$, and a constant $C_1 \ge 0$. Assume the decay hypothesis [eq:hfbound] for the taper transform $\hat\varphi_T$ (the paper Fourier transform $\hat\varphi(z) = \int\varphi(u)e^{izu}\,du$ of the taper $\varphi$): for all real $r, y$ with $|y| \le 1/2$ and $r - iy \ne 0$,
--   $$\|\hat\varphi_T(r - iy)\| \;\le\; \frac{e^{L/4}\,C_1}{\|r - iy\|^{2}}.$$
--   Let $\rho$ be a zero of the configuration whose ordinate $\gamma_\rho = \operatorname{Im}\rho$ is in the tail (`InTail T ρ.im`: $\gamma_\rho \le T - \sqrt T$ or $\gamma_\rho > 2T + \sqrt T$), and let $k < d$ be a grid index with grid point $\tau_k = T + k\cdot 2\pi/L$. The entry $u_\rho(k)$ is $\hat\varphi_T(\gamma_\rho - \tau_k)$, evaluated at the complex point $\gamma_\rho - \tau_k$ where $\gamma_\rho$ is the full complex expression: writing $\rho = \beta + i\gamma$, one has $\gamma_\rho - \tau_k = (\gamma - \tau_k) - iy$ with $y = \beta - 1/2$, and $|y| \le 1/2$ since $0 < \beta < 1$ — the only place the critical strip is used.
--
--   **Statement.**
--   $$\|u_\rho(k)\| \;\le\; \bigl(e^{L/4}\,C_1\bigr)\cdot \Bigl|\gamma_\rho - \bigl(T + k\cdot\tfrac{2\pi}{L}\bigr)\Bigr|^{-2},$$
--   i.e. the paper's "$|\hat\varphi(r - iy)| \le e^{L/4}\|\varphi''\|_1 |r-iy|^{-2} \le X^{1/4}C_1\, r^{-2}$" specialized to the entries of $u_\rho$.
--
--   **Role.** This is the entrywise input to `norm_sq_uvec_le` in `Zeta23.Tail`, and thereby to the whole tail bound of Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L187-L227, docstring tag [eq:hfbound]

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

theorem Zeta23.Tail.norm_uvec_le (hL : 0 < P.L T) (hT : 0 < T) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hdecay : ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
        ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ / ‖(r : ℂ) - I * y‖ ^ 2)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (htail : InTail T ρ.im) (k : Fin (P.d T)) :
    ‖uvec P T ρ k‖
      ≤ (Real.exp (P.L T / 4) * C₁) * (|ρ.im - (T + (k : ℕ) * (2 * Real.pi / P.L T))| ^ 2)⁻¹ := by sorry
