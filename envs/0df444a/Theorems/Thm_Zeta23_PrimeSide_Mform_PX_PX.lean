-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Mform_PX_PX
-- name    : Zeta23.PrimeSide.Mform_PX_PX
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:03:35.568153+00:00
-- url     : https://prove2.me/theorems/61b6fc71-1bc7-4942-b58e-ae3097c3650a
-- title:
--   Decomposition $\mathcal M[P_X, P_X] = \mathcal D + \mathcal O_1 + \mathcal O_2$ [eq:MPP]
-- statement:
--   Here $\mathcal M[u_1,u_2] := \iint_{I\times I} \Phi(\tau-\tau')^2\,u_1(\tau)\,u_2(\tau')\,d\tau\,d\tau'$ with window $I = [T,2T]$ (`Mform`), and $P_X(\tau) = -\tfrac1\pi \sum_{n \le X} a_n \cos(\tau y_n)$ with $a_n = \Lambda(n)/\sqrt n$, $y_n = \log n$ [eq:Pdef]. $A^-$ and $A^+$ (`Aminus`, `Aplus`) are the difference- and sum-frequency kernels: $A^\mp(y,y') = \int_{[-T,T]} \Phi(x)^2\,J^\mp(x)\,dx$, where $J^\mp(x)$ is the inner integral $\int \cos$ over the sheared window $I \cap (I - x)$ at frequency $y - y'$, respectively $y + y'$.
--
--   For $T \ge 0$, $\Phi$ continuous, and any real $X$, bilinearity in the prime sum plus the per-pair decomposition `Mform_cos_cos` give
--   $$\mathcal M[P_X,P_X] = \frac{1}{2\pi^2}\Bigl(\underbrace{\sum_{n \le X} a_n^2\,A^-(y_n,y_n)}_{\mathcal D} + \underbrace{\sum_{n \ne m} a_n a_m\,A^-(y_n,y_m)}_{\mathcal O_1} + \underbrace{\sum_{n,m} a_n a_m\,A^+(y_n,y_m)}_{\mathcal O_2}\Bigr),$$
--   all sums over integers $0 < n,m \le \lfloor X\rfloor$, the $\mathcal O_1$ sum omitting $n = m$.
--
--   This is [eq:MPP] (§5.4), the entry point of `prop_PP`: the three pieces are then estimated by `diag_estimate`, `O1_bound` and `O2_estimate` to evaluate the $P\times P$ contribution to the second moment $\mathcal M$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean#L182-L245, docstring tag [eq:MPP]

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
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ lam : ℝ}
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.Mform_PX_PX (hT : 0 ≤ T) (hΦ : Continuous Φ) (X : ℝ) :
    Mform Φ T (Zeta23.PX X) (Zeta23.PX X)
      = (1 / (2 * π ^ 2)) *
        ((∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
          + (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m)))
          + ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
              acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)) := by sorry
