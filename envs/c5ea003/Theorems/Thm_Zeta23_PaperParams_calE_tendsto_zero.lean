-- Prove2me | Theorems.Thm_Zeta23_PaperParams_calE_tendsto_zero
-- name    : Zeta23.PaperParams.calE_tendsto_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:57:27.797502+00:00
-- url     : https://prove2.me/theorems/efa45f5c-8aba-448a-8b08-b696d6063a62
-- title:
--   The trace error term $\mathcal{E}_T \to 0$ as $T \to \infty$
-- statement:
--   Fix a parameter bundle $P$ (a `Params`: a taper profile $\varrho$, an exponent $\lambda$, and a taper width $w$). For $T$ write $l = \log\frac{T}{2\pi}$, $L = \lambda l$, and $X = e^L = (T/2\pi)^\lambda$. The error quantity of the paper's [thm:traces] is
--   $$\mathcal{E}_T \;:=\; \frac{w}{L} \;+\; \frac{(l^2 + X)\,\log l}{T\, l} \;+\; T^{\lambda/2 - 1}.$$
--   The theorem asserts: if $0 < \lambda \le 1$ and $w \ge 0$, then
--   $$\mathcal{E}_T \;\longrightarrow\; 0 \qquad (T \to \infty),$$
--   stated as `Tendsto P.calE atTop (𝓝 0)`. This packages the paper's estimates "$\mathcal{E}_T \ll_\lambda w/L + T^{\lambda-1}\log l$ ($\lambda < 1$), $\mathcal{E}_T \ll w/L + \log l / l$ ($\lambda = 1$)" together with $L = \lambda l \to \infty$: each of the three summands is shown to vanish in the limit ($w/L \to 0$, the middle term is eventually at most $l^2/T + \log l/l$, and $T^{\lambda/2-1} \to 0$ since $\lambda \le 1$).
--
--   In the module `Zeta23.PrimeSideB` this is the statement that the error in the trace computations of the prime side is asymptotically negligible; its consumer is `Zeta23.PrimeSide.ratio`, the prime-side trace ratio feeding the matrix-variational argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L263-L307, docstring tag [thm:traces]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideTemp

open Real Filter Asymptotics Topology
open Zeta23
open PaperParams
variable (P : Params)
variable {P}

theorem Zeta23.PaperParams.calE_tendsto_zero (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hw : 0 ≤ P.w) :
    Tendsto P.calE atTop (𝓝 0) := by sorry
