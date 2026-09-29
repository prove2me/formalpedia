-- Prove2me | Theorems.Thm_Zeta23_MV_norm_B_le_sqrt
-- name    : Zeta23.MV.norm_B_le_sqrt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:54:04.549785+00:00
-- url     : https://prove2.me/theorems/4e7d2e9a-0496-447e-aa8a-ff9fa6e2ff48
-- title:
--   Bilinear bound $\|B(x,z)\| \le 2C\sqrt{N_2(x)}\sqrt{N_2(z)}$ from a diagonal bound
-- statement:
--   Let $\iota$ be a finite index type, let $\lambda \colon \iota \to \mathbb{R}$ be a family of frequencies (`freq`), and let $\delta \colon \iota \to \mathbb{R}$ be weights with $\delta_r > 0$ for every $r$. For complex vectors $x, z \colon \iota \to \mathbb{C}$ write
--   $$B(x,z) \;=\; \sum_{r \ne s} \frac{x_r \overline{z_s}}{\lambda_r - \lambda_s}, \qquad N_2(x) \;=\; \sum_r \frac{|x_r|^2}{\delta_r}$$
--   for the Hilbert-type sesquilinear form (with coefficient $0$ on the diagonal) and the weighted $\ell^2$ quantity.
--
--   Suppose $C \ge 0$ and the *diagonal* bound $\|B(y,y)\| \le C \cdot N_2(y)$ holds for every $y \colon \iota \to \mathbb{C}$. Then for all $x, z$,
--   $$\|B(x,z)\| \;\le\; 2C\, \sqrt{N_2(x)}\, \sqrt{N_2(z)}.$$
--   The proof first uses polarization to get $\|B(x,z)\| \le C\,(N_2(x) + N_2(z))$, then the scaling invariance $B(tx, t^{-1}z) = B(x,z)$ together with AM–GM to reach the geometric-mean form.
--
--   This is Step 2 of the derivation, in the module `Zeta23.MV`, of the bilinear Montgomery–Vaughan inequality from its literature (diagonal) form; it feeds directly into `Zeta23.MVHilbert_of_diag`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV.lean#L189-L217

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

theorem Zeta23.MV.norm_B_le_sqrt {C : ℝ} (hC : 0 ≤ C) {freq δ : ι → ℝ} (hδ : ∀ r, 0 < δ r)
    (hdiag : ∀ y : ι → ℂ, ‖B freq y y‖ ≤ C * N2 δ y) (x z : ι → ℂ) :
    ‖B freq x z‖ ≤ 2 * C * Real.sqrt (N2 δ x) * Real.sqrt (N2 δ z) := by sorry
