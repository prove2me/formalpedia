-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_inner_cos_cos
-- name    : Zeta23.PrimeSide.inner_cos_cos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:02:46.323374+00:00
-- url     : https://prove2.me/theorems/7d0057fd-a4f0-456c-b6fb-3abab869aad6
-- title:
--   Closed form of the inner cosine integral over the sheared window
-- statement:
--   Here $I = [T, 2T]$, and for an offset $x$ the sheared window is $I_x = I \cap (I - x) = [\alpha, \beta]$ with $\alpha = \max(T - x, T)$ and $\beta = \min(2T - x, 2T)$. The elementary kernel $J(\theta, c; \alpha, \beta)$ is the closed form of $\int_\alpha^\beta \cos(\theta t + c)\, dt$: equal to $(\beta - \alpha)\cos c$ when $\theta = 0$, and to $\bigl(\sin(\theta\beta + c) - \sin(\theta\alpha + c)\bigr)/\theta$ otherwise. Assume $T \ge 0$ and $|x| \le T$. Then for all frequencies $y, y'$,
--   $$\int_{I_x} \cos\bigl((x + \tau') y\bigr)\, \cos(\tau' y')\, d\tau' \;=\; \tfrac12\, J\bigl(y - y',\, xy;\, \alpha, \beta\bigr) \;+\; \tfrac12\, J\bigl(y + y',\, xy;\, \alpha, \beta\bigr).$$
--   This is the inner integral of [eq:MPP] in closed form: the product-to-sum identity $\cos A \cos B = \tfrac12(\cos(A - B) + \cos(A + B))$ splits it into a difference-frequency and a sum-frequency piece, each a linear-phase cosine integral.
--
--   It feeds `Mform_cos_cos`, the per-frequency-pair decomposition $\mathcal{M}[\cos(\cdot\, y), \cos(\cdot\, y')] = A^-(y,y') + A^+(y,y')$ used to evaluate the prime–prime term $\mathcal{M}[P_X, P_X]$ in [prop:PP] (module `Zeta23.PrimeSideB.PPKernel`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L262-L279, docstring tag [eq:MPP]

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
variable {T : ℝ}

theorem Zeta23.PrimeSide.inner_cos_cos (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) (y y' : ℝ) :
    ∫ τ' in Ix T x, Real.cos ((x + τ') * y) * Real.cos (τ' * y')
      = (Jker (y - y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
          + Jker (y + y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))) / 2 := by sorry
