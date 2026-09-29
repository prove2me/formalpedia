-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_Aplus_le
-- name    : Zeta23.PrimeSide.abs_Aplus_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:05:27.434284+00:00
-- url     : https://prove2.me/theorems/0b2c395e-d0fa-4342-93ed-e8a563c87ebb
-- title:
--   Sum-frequency kernel bound: $|A^+(y,y')| \le \frac{2}{y+y'}\int\Phi^2$
-- statement:
--   Here $A^+(y,y') = \int_{[-T,T]}\Phi(x)^2 J^+(x)\,dx$ (`Aplus`) is the sum-frequency kernel of the $P\times P$ decomposition, $J^+(x)$ being the closed form of the inner integral $\int\cos$ at frequency $y + y'$ over the sheared window $I \cap (I - x)$, $I = [T,2T]$.
--
--   Assume $\Phi$ is continuous with $\Phi^2$ integrable, and let $y, y'$ be reals with $y + y' > 0$. Then
--   $$|A^+(y,y')| \;\le\; \frac{2}{y+y'}\int_{\mathbb R}\Phi(x)^2\,dx,$$
--   since the oscillatory inner integral obeys $|J^+| \le 2/(y+y')$ — the formal counterpart of §5.4's "$|\int(nm)^{i\tau'}\,d\tau'| \le 2/\log(nm)$".
--
--   Applied at $y = \log n$, $y' = \log m$ (where $y + y' \ge 2\log 2$ once the vanishing $n = 1, m = 1$ terms are discarded), it is the per-pair input to `O2_estimate`, the bound for the term $\mathcal O_2$ in [prop:PP] (module `Zeta23.PrimeSideB.PPKernel`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L386-L408

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

theorem Zeta23.PrimeSide.abs_Aplus_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {y y' : ℝ}
    (hyy : 0 < y + y') :
    |Aplus Φ T y y'| ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by sorry
