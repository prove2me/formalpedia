-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_Mform_le
-- name    : Zeta23.PrimeSide.abs_Mform_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:11:59.739135+00:00
-- url     : https://prove2.me/theorems/70620c27-42f3-4a40-9981-711b8bb01447
-- title:
--   Sup-bound for the seam form: $|\mathcal{M}[u, v]| \le B_u B_v\, T \int \Phi^2$
-- statement:
--   For a weight $\Phi : \mathbb{R} \to \mathbb{R}$ and a height $T$, the bilinear seam form of Section 5.4 is
--   $$\mathcal{M}[u_1, u_2] \;=\; \iint_{I \times I} \Phi(\tau - \tau')^2\, u_1(\tau)\, u_2(\tau')\, d\tau\, d\tau', \qquad I = [T, 2T].$$
--   Assume $T \ge 0$, $\Phi$, $u$, $v$ continuous with $\Phi^2$ integrable, and suppose $|u| \le B_u$ and $|v| \le B_v$ on $I$. Then
--   $$\bigl|\mathcal{M}[u, v]\bigr| \;\le\; B_u\, B_v \cdot T \int_{\mathbb{R}} \Phi(x)^2\, dx.$$
--   This is the trivial estimate of the [prop:cross] proof (Section 5.4): insert the sup bounds into the definition of $\mathcal{M}$, an integral over a region of $\tau'$-length at most $T$ for each $\tau$.
--
--   In the project it produces three of the four cross-term bounds of [prop:cross]: it is consumed by `prop_cross_PPi` ($\mathcal{M}[P_X, \Pi_X] \ll LX$), `prop_cross_PiPi` ($\mathcal{M}[\Pi_X, \Pi_X] \ll LX/T$), and `prop_cross_muPi` ($\mathcal{M}[\mu, \Pi_X] \ll lL\sqrt{X}$), which feed the trace assembly of [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L236-L279, docstring tag [prop:cross]

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
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.abs_Mform_le (hT : 0 ≤ T) (hΦ : Continuous Φ) {u v : ℝ → ℝ} (hu : Continuous u)
    (hv : Continuous v) (hΦint : Integrable (fun x => Φ x ^ 2)) {Bu Bv : ℝ}
    (hBu : ∀ τ ∈ Set.Icc T (2 * T), |u τ| ≤ Bu) (hBv : ∀ τ ∈ Set.Icc T (2 * T), |v τ| ≤ Bv) :
    |Mform Φ T u v| ≤ Bu * Bv * (T * ∫ x, Φ x ^ 2) := by sorry
