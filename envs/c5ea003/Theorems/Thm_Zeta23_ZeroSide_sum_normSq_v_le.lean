-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_sum_normSq_v_le
-- name    : Zeta23.ZeroSide.sum_normSq_v_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:50.291581+00:00
-- url     : https://prove2.me/theorems/a8139db0-7b34-4beb-8303-3f0e7a86a54a
-- title:
--   Finite Poisson bound: $\sum_{0 \le k < d} |\hat\varphi(\gamma_\rho - \tau_k)|^2 \le aL^2$ for on-line zeros
-- statement:
--   Fix an abstract zero configuration $Z$, a height $T$, and parameters $P = (\varrho, \lambda, w)$, with $L = \lambda \log(T/2\pi)$, taper $\varphi$, grid points $\tau_k = T + k \cdot 2\pi/L$, dimension $d = \lfloor LT/2\pi \rfloor$, and $a = L^{-1} \int \varphi^2$ [eq:abdef]. The hypotheses are the three analytic inputs of the block section: `PhiHatConj` ($\hat\varphi(\bar z) = \overline{\hat\varphi(z)}$), `PhiHatReal` ($\hat\varphi$ is real on $\mathbb{R}$), and `PoissonSq` (the consequence of [lem:poisson]: for every real $\gamma$, $\sum_{k \in \mathbb{Z}} \hat\varphi(\gamma - \tau_k)^2 = aL^2$ as a `HasSum`).
--
--   Let $\rho$ be a member of the finite zero set $\mathcal{Z}(I')$ (zeros with ordinate in $(T - D_0, 2T + D_0]$, $D_0 = \sqrt{T}$) which lies in the `onLine` part of the block data, i.e. is fixed by the reflection $\rho \mapsto 1 - \bar\rho$, equivalently $\operatorname{Re} \rho = 1/2$. Writing $v_\rho(k) = \hat\varphi(\gamma_\rho - \tau_k)$ for the evaluation vector (with $\gamma_\rho = (\rho - 1/2)/i$, real for on-line $\rho$), the assertion is
--   $$\sum_{0 \le k < d} \|v_\rho(k)\|^2 \;\le\; a\,L^2:$$
--   the finite sum over the $d$ grid indices is at most the value $aL^2$ of the full sum over $k \in \mathbb{Z}$, since all terms are nonnegative.
--
--   This is the key trace estimate behind prop:block(ii), "$\operatorname{tr} P \le N_{\mathrm{on}}(I')$": it bounds each on-line zero's contribution to the trace of the positive-semidefinite part of the block decomposition. It is consumed by `Zeta23.ZeroSide.blockInputsAt` in `Zeta23.ZeroSide`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L906-L924, docstring tag [lem:poisson]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide

set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
open Zeta23 Classical
variable (Z : ZeroConfig) (T : ℝ)
variable (P : Params)
variable {Z T P}
variable (Z T P)

theorem Zeta23.ZeroSide.sum_normSq_v_le (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (z : ZI Z T) (hz : z ∈ (blockData Z T P hconj).onLine) :
    ∑ k, ‖(blockData Z T P hconj).v z k‖ ^ 2 ≤ P.a T * P.L T ^ 2 := by sorry
