-- Prove2me | Theorems.Thm_Zeta23_MVHilbert_of_diag
-- name    : Zeta23.MVHilbert_of_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:54:10.540142+00:00
-- url     : https://prove2.me/theorems/2de8df1a-f116-45b7-8527-7865c652b214
-- title:
--   Bilinear Montgomery–Vaughan inequality from the diagonal form: $\mathrm{MVDiag}\,C \Rightarrow \mathrm{MVHilbert}\,(2C)$
-- statement:
--   Two forms of the Montgomery–Vaughan weighted Hilbert inequality are in play. `MVDiag`$\,C$ is the literature (diagonal) form: for every finite family of *distinct* real frequencies $\lambda_r$ and admissible gaps $\delta_r$ (meaning $0 < \delta_r$ and $\delta_r \le |\lambda_r - \lambda_s|$ for all $s \ne r$) and all complex $x_r$,
--   $$\Bigl| \sum_{r \ne s} \frac{x_r \overline{x_s}}{\lambda_r - \lambda_s} \Bigr| \;\le\; C \sum_r \frac{|x_r|^2}{\delta_r}.$$
--   `MVHilbert`$\,C'$ is the bilinear form used by the project's hypotheses layer: under the same admissibility conditions, for all complex $x_r, z_r$,
--   $$\Bigl| \sum_{r \ne s} \frac{x_r \overline{z_s}}{\lambda_r - \lambda_s} \Bigr| \;\le\; C' \Bigl(\sum_r \frac{|x_r|^2}{\delta_r}\Bigr)^{1/2} \Bigl(\sum_r \frac{|z_r|^2}{\delta_r}\Bigr)^{1/2}.$$
--   The theorem asserts: if $C \ge 0$ and `MVDiag`$\,C$ holds, then `MVHilbert`$\,(2C)$ holds. This is the paper's [lem:MV] "In general …" step, carried out by polarization plus scaling rather than through the operator norm of $\Delta H \Delta$; the constant is $2C$ rather than $C$, which is immaterial since only $\exists C$ is ever used (in the published inequality one may take $C = 3\pi/2$).
--
--   The bilinear inequality is the form consumed by the mollified second-moment / matrix-variational core of the project: this node feeds directly into the headline assembly theorems `Zeta23.thmA3` and `Zeta23.thmA3_cumulative`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV.lean#L221-L232, docstring tag [lem:MV]

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

theorem Zeta23.MVHilbert_of_diag {C : ℝ} (hC : 0 ≤ C) (h : MVDiag C) : MVHilbert (2 * C) := by sorry
