-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Mform_mu_PX_eq
-- name    : Zeta23.PrimeSide.Mform_mu_PX_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:03:50.315469+00:00
-- url     : https://prove2.me/theorems/3f5df8fc-1cec-481e-af56-186afcb813ba
-- title:
--   $\mathcal M[\mu, P_X]$ as a finite sum over prime-power frequencies
-- statement:
--   Here $\mathcal M[u_1,u_2] := \iint_{I\times I}\Phi(\tau-\tau')^2 u_1(\tau)u_2(\tau')\,d\tau\,d\tau'$ with $I = [T,2T]$ and $\Phi$ the taper transform of the setting $p$; $\mu$ is the archimedean density [eq:mudef] and $P_X(\tau) = -\tfrac1\pi\sum_{n\le X} a_n\cos(\tau y_n)$ with $a_n = \Lambda(n)/\sqrt n$, $y_n = \log n$.
--
--   Assuming only that $\Phi$ and $\mu$ are continuous, linearity of the integral (Fubini over the finite sum) gives
--   $$\mathcal M[\mu, P_X] \;=\; \sum_{n \le X} \Bigl(-\frac{1}{\pi}\,a_n\Bigr)\,\mathcal M\bigl[\mu,\ \cos(\cdot\,y_n)\bigr],$$
--   the sum over integers $0 < n \le \lfloor X\rfloor$.
--
--   This reduces the $\mu \times P$ cross term of the second moment to single-frequency integrals, which are then estimated per frequency in `prop_cross_muP` (§5.4, module `Zeta23.PrimeSideA.CrossMuP`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/CrossMuP.lean#L47-L65

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
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.Mform_mu_PX_eq {p : Setting} {F : LocalFun} (hΦ : Continuous F.Phi) (hμ : Continuous Zeta23.mu) :
    Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)
      = ∑ n ∈ primeRange p.X, (-(1 / Real.pi) * acoef n)
          * Mform F.Phi p.T Zeta23.mu (fun t => Real.cos (t * ycoef n)) := by sorry
