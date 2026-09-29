-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Mform_cos_cos
-- name    : Zeta23.PrimeSide.Mform_cos_cos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:03:19.63143+00:00
-- url     : https://prove2.me/theorems/f6eccb0f-38e0-46c1-a529-810ebe5241db
-- title:
--   $\mathcal M[\cos(\cdot\,y), \cos(\cdot\,y')] = \tfrac12\bigl(A^-(y,y') + A^+(y,y')\bigr)$
-- statement:
--   With $\mathcal M[u_1,u_2] := \iint_{I\times I}\Phi(\tau-\tau')^2 u_1(\tau)u_2(\tau')\,d\tau\,d\tau'$, $I = [T,2T]$, the theorem computes $\mathcal M$ on a pair of pure cosines: for $T \ge 0$, $\Phi$ continuous, and $y, y' \in \mathbb R$,
--   $$\mathcal M[\cos(\cdot\,y), \cos(\cdot\,y')] = \frac{A^-(y,y') + A^+(y,y')}{2},$$
--   where $A^\mp(y,y') := \int_{[-T,T]}\Phi(x)^2\,J^\mp(x)\,dx$ and $J^\mp(x)$ is the closed form (`Jker`) of the inner integral $\int_{I \cap (I-x)} \cos((x+\tau')y)\cos(\tau'y')\,d\tau'$ at the difference frequency $y - y'$, respectively the sum frequency $y + y'$. The proof shears the double integral by $\tau = x + \tau'$ and splits $\cos A\cos B = \tfrac12(\cos(A-B) + \cos(A+B))$.
--
--   This per-frequency-pair identity ([eq:MPP], §5.4) is the building block of `Mform_PX_PX`, the $\mathcal D + \mathcal O_1 + \mathcal O_2$ decomposition of the $P\times P$ second-moment term.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L311-L334, docstring tag [eq:MPP]

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
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.Mform_cos_cos (hT : 0 ≤ T) (hΦ : Continuous Φ) (y y' : ℝ) :
    Mform Φ T (fun τ => Real.cos (τ * y)) (fun τ => Real.cos (τ * y'))
      = (Aminus Φ T y y' + Aplus Φ T y y') / 2 := by sorry
