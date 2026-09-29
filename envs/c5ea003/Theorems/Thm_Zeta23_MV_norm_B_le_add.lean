-- Prove2me | Theorems.Thm_Zeta23_MV_norm_B_le_add
-- name    : Zeta23.MV.norm_B_le_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:53:29.022563+00:00
-- url     : https://prove2.me/theorems/5bfdcf23-0d69-409a-817f-2afc4524e6c6
-- title:
--   Polarization step: $\|B(x,z)\| \le C\,(N_2(x) + N_2(z))$ from the diagonal bound
-- statement:
--   Let $\iota$ be a finite index type, $\mathrm{freq}, \delta \colon \iota \to \mathbb{R}$, and let $B(x, z) = \sum_{r \ne s} x_r\, \overline{z_s}\,/(\mathrm{freq}_r - \mathrm{freq}_s)$ be the Montgomery–Vaughan sesquilinear form and $N_2(y) = \sum_r \|y_r\|^2/\delta_r$ the weighted $\ell^2$-quantity. Let $C \ge 0$ and assume the diagonal bound: $\|B(y, y)\| \le C\, N_2(y)$ for every $y \colon \iota \to \mathbb{C}$. Then for all $x, z \colon \iota \to \mathbb{C}$,
--
--   $$\|B(x, z)\| \;\le\; C\,\bigl(N_2(x) + N_2(z)\bigr).$$
--
--   The proof polarizes: $4\,B(x,z) = B(x+z,x+z) - B(x-z,x-z) + i\,B(x+iz,x+iz) - i\,B(x-iz,x-iz)$, bounds each term by the diagonal hypothesis, and applies the parallelogram law `N2_polar` for the four weighted norms.
--
--   **Role.** Step 1 of deriving the bilinear Montgomery–Vaughan inequality (the H-MV hypothesis of `Zeta23.Hypotheses`) from the published diagonal ($z = x$) form: it is consumed by `Zeta23.MV.norm_B_le_sqrt`, which upgrades the additive bound to the geometric-mean form $2C\sqrt{N_2(x)}\sqrt{N_2(z)}$ by the scaling $x \mapsto tx$, $z \mapsto z/t$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV.lean#L164-L187

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

theorem Zeta23.MV.norm_B_le_add {C : ℝ} (_hC : 0 ≤ C) {freq δ : ι → ℝ}
    (hdiag : ∀ y : ι → ℂ, ‖B freq y y‖ ≤ C * N2 δ y) (x z : ι → ℂ) :
    ‖B freq x z‖ ≤ C * (N2 δ x + N2 δ z) := by sorry
