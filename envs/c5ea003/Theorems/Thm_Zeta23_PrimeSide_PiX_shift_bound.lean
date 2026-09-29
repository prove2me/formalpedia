-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_PiX_shift_bound
-- name    : Zeta23.PrimeSide.PiX_shift_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:07:08.869861+00:00
-- url     : https://prove2.me/theorems/756f5e52-733c-4f58-b90b-f5b8bee1e080
-- title:
--   Shifted pole-term bound: $|\Pi_X(t+r)| \le 6\sqrt X/t + 12\sqrt X\,r^2/t^2$
-- statement:
--   Here $\Pi_X$ is the pole-term density [eq:Pidef], and the window-generic package `LocalHypsCore` supplies the fact [eq:PiPfacts] (§2.1) that $|\Pi_X(\tau)| \le 3\sqrt X/(1+|\tau|)$, with $X$ the setting's prime cutoff.
--
--   The theorem shifts this bound to a translate: for every $t \ge 2$ and every real $r$,
--   $$|\Pi_X(t+r)| \;\le\; \frac{6\sqrt X}{t} + \frac{12\sqrt X\,r^2}{t^2}.$$
--   For $|r| \le t/2$ one has $1 + |t+r| \ge t/2$ and the first term suffices; for $|r| > t/2$ the factor $(2|r|/t)^2 > 1$ lets the second term absorb the trivial bound (§5.2: "$|\Pi_X(\tau)| \le 6\sqrt X/T$ for $|\tau - \tau_k| \le T/2$", tail absorbed).
--
--   It is consumed by `Pi_part_bound`, the estimate of the $\Pi$-part $G^\Pi_{kk}$ of a diagonal Gram entry in the trace asymptotics [prop:trace].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1080-L1107, docstring tag [eq:PiPfacts]

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
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.PiX_shift_bound (hF : LocalHypsCore cϱ p F) {t : ℝ} (ht : 2 ≤ t) (r : ℝ) :
    |Zeta23.PiX p.X (t + r)| ≤ 6 * Real.sqrt p.X / t + 12 * Real.sqrt p.X * r ^ 2 / t ^ 2 := by sorry
