-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_tr2_first
-- name    : Zeta23.PrimeSide.tr2_first
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:37:26.692567+00:00
-- url     : https://prove2.me/theorems/7a5b6f1d-439a-4e1f-aa49-edfd3c62f57c
-- title:
--   Trace asymptotics [eq:tr2], first form: $\operatorname{tr}\tilde G^2 = 2\pi b L \int_T^{2T}\mu^2 + \frac{T}{\pi}\sum_{n\le X}\frac{\Lambda(n)^2}{n}g(\log n) + O(\cdots)$
-- statement:
--   Fix parameters $P = (\varrho, \lambda, w)$ — a taper profile $\varrho$, an exponent $\lambda$ with $0 < \lambda \le 1$, and a ramp width $w \ge 1$. For $T > 0$ write $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, $\ell_1 = l + 2\log 2 - 1$, and let $$\mathcal{E}_T \;=\; \frac{w}{L} + \frac{(l^2 + X)\log l}{T\,l} + T^{\lambda/2 - 1}$$ be the error parameter of Theorem [thm:traces]. The statement is parametric in abstract data $D$: real-valued functions of $T$ standing for the quantities of the paper's §5, among them $\operatorname{tr}\tilde G(T)$ (the trace of the normalized prime-side matrix $\tilde G = G/L$, $G_{kl} = \int_{\mathbb R} \hat\varphi(\tau - \tau_k)\hat\varphi(\tau - \tau_l)\,\nu_X(\tau)\,d\tau$, the second expression of [eq:Gdef]), $\operatorname{tr}\tilde G^2(T)$, and $N(T,2T)$ (the number of nontrivial zeros of $\zeta$ with ordinate in $(T, 2T]$, with multiplicity). `EvBound f g` is the explicit-constant big-$O$: there exist $C > 0$ and $T_0$ such that $|f(T)| \le C\,g(T)$ for all $T \ge T_0$. The theorem carries the standing hypothesis `Facts D`: the conclusions of the §5 sub-results ([prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]) together with the classical inputs [eq:RvM], [eq:muints] and the taper bounds [eq:abdef], each in `EvBound` form on the data $D$.
--
--   Besides $\operatorname{tr}\tilde G^2$, the statement involves three further components of the data $D$: $b(T)$, standing for the taper constant $b = L^{-1}\int \varphi^4$ of [eq:abdef]; $\int_T^{2T}\mu(\tau)^2\,d\tau$, the second moment of the archimedean density $\mu$ of [eq:mudef]; and the weighted prime sum $\sum_{n \le X}\Lambda(n)^2 n^{-1} g(\log n)$ of [prop:PP], where $\Lambda$ is the von Mangoldt function and $g$ the weight arising from the taper.
--
--   **Statement.** Under `Facts D`, the first form of [eq:tr2] holds:
--
--   $$\operatorname{tr}\tilde G^2 \;=\; 2\pi\, b\, L \int_T^{2T} \mu(\tau)^2\,d\tau \;+\; \frac{T}{\pi}\sum_{n \le X}\frac{\Lambda(n)^2}{n}\, g(\log n) \;+\; O\bigl(L\, l\, (\log l)\, (l^2 + X)\bigr),$$
--
--   the $O$-term being an `EvBound`: there exist $C > 0$ and $T_0$ such that for $T \ge T_0$ the difference is at most $C \cdot L\, l \,(\log l)\,(l^2 + X)$ in absolute value.
--
--   **Role.** An intermediate step of `Zeta23.PrimeSideB`: it is assembled from the bilinear expansion [eq:Msplit] of $\mathcal M = \mathcal M[\nu_X,\nu_X]$, the diagonal evaluations [prop:mumu] and [prop:PP], and the cross-term bounds [prop:cross], all fields of `Facts D`. Its sole consumer is `Zeta23.PrimeSide.tr2`, which upgrades it to the second form of [eq:tr2].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L483-L540, docstring tag [eq:tr2]

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
open PrimeSide
open PaperParams
variable {P : Params} (D : Data P)
variable {D} (h : Facts D)
include h

theorem Zeta23.PrimeSide.tr2_first : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumL2g T))
    (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by sorry
