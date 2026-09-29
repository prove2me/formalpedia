-- Prove2me | Theorems.Thm_Zeta23_MV_N2_polar
-- name    : Zeta23.MV.N2_polar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:51:41.392974+00:00
-- url     : https://prove2.me/theorems/d2599d12-f96b-48d6-a381-d653000a3725
-- title:
--   Parallelogram law for the weighted norm: $\sum_{\pm,\pm i} N_2 = 4(N_2(x) + N_2(z))$
-- statement:
--   Let $\iota$ be a finite index type, $\delta \colon \iota \to \mathbb{R}$ any weight family, and $x, z \colon \iota \to \mathbb{C}$. Write $N_2(\delta, y) = \sum_r \|y_r\|^2/\delta_r$ for the weighted $\ell^2$-quantity of the Montgomery–Vaughan inequality. Then the four polarization vectors satisfy
--
--   $$N_2(\delta, x+z) + N_2(\delta, x-z) + N_2(\delta, x + iz) + N_2(\delta, x - iz) \;=\; 4\,\bigl(N_2(\delta, x) + N_2(\delta, z)\bigr).$$
--
--   This is the parallelogram law in $\mathbb{C}$ applied termwise ($\|a+b\|^2 + \|a-b\|^2 = 2\|a\|^2 + 2\|b\|^2$, twice), divided by the weights; no hypotheses on $\delta$ are needed.
--
--   **Role.** In `Zeta23.MV` this powers the polarization step that derives the bilinear Montgomery–Vaughan inequality from the published diagonal ($z = x$) form: it is consumed by `Zeta23.MV.norm_B_le_add`, giving $\|B(x,z)\| \le C\,(N_2(x) + N_2(z))$ from the diagonal bound.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV.lean#L99-L117

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
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
import Definitions.Def_Zeta23_MV

open Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23
open MV
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem Zeta23.MV.N2_polar (δ : ι → ℝ) (x z : ι → ℂ) :
    N2 δ (x + z) + N2 δ (x - z) + N2 δ (x + I • z) + N2 δ (x - I • z)
      = 4 * (N2 δ x + N2 δ z) := by sorry
