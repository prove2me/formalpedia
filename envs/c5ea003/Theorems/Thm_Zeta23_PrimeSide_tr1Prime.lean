-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_tr1Prime
-- name    : Zeta23.PrimeSide.tr1Prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:37:16.83198+00:00
-- url     : https://prove2.me/theorems/dfb17d76-7848-4336-8a65-6ffaba969a2a
-- title:
--   Trace asymptotics [eq:tr1], second form: $\operatorname{tr}\tilde G = L\,N(T,2T)\,(1 + O(\mathcal{E}_T))$
-- statement:
--   Fix parameters $P = (\varrho, \lambda, w)$ — a taper profile $\varrho$, an exponent $\lambda$ with $0 < \lambda \le 1$, and a ramp width $w \ge 1$. For $T > 0$ write $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, $\ell_1 = l + 2\log 2 - 1$, and let $$\mathcal{E}_T \;=\; \frac{w}{L} + \frac{(l^2 + X)\log l}{T\,l} + T^{\lambda/2 - 1}$$ be the error parameter of Theorem [thm:traces]. The statement is parametric in abstract data $D$: real-valued functions of $T$ standing for the quantities of the paper's §5, among them $\operatorname{tr}\tilde G(T)$ (the trace of the normalized prime-side matrix $\tilde G = G/L$, $G_{kl} = \int_{\mathbb R} \hat\varphi(\tau - \tau_k)\hat\varphi(\tau - \tau_l)\,\nu_X(\tau)\,d\tau$, the second expression of [eq:Gdef]), $\operatorname{tr}\tilde G^2(T)$, and $N(T,2T)$ (the number of nontrivial zeros of $\zeta$ with ordinate in $(T, 2T]$, with multiplicity). `EvBound f g` is the explicit-constant big-$O$: there exist $C > 0$ and $T_0$ such that $|f(T)| \le C\,g(T)$ for all $T \ge T_0$. The theorem carries the standing hypothesis `Facts D`: the conclusions of the §5 sub-results ([prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]) together with the classical inputs [eq:RvM], [eq:muints] and the taper bounds [eq:abdef], each in `EvBound` form on the data $D$.
--
--   **Statement.** Under `Facts D`, the second equality of [eq:tr1] holds:
--
--   $$\operatorname{tr}\tilde G \;=\; L\,N(T,2T)\,\bigl(1 + O(\mathcal{E}_T)\bigr),$$
--
--   formalized as: there exist $C > 0$ and $T_0$ such that for all $T \ge T_0$, $\bigl|\operatorname{tr}\tilde G(T) - L\,N(T,2T)\bigr| \le C\,\mathcal{E}_T\cdot L\,N(T,2T)$.
--
--   **Role.** Proved in `Zeta23.PrimeSideB` from the first equality $\operatorname{tr}\tilde G = a L N(T,2T) + O(L\sqrt X)$ (the `prop_trace` field of `Facts`), the taper bounds $1 - 2w/L \le a \le 1$ of [eq:abdef], the lower bound $N(T,2T) \gg T\,l$ coming from the Riemann–von Mangoldt input [eq:RvM], and $\sqrt X \le T^{\lambda/2}$. It feeds the ratio asymptotics [eq:ratio] (`Zeta23.PrimeSide.ratio`) and the final assembly `Zeta23.PrimeSide.tracesBounds_of_facts` of Theorem [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L433-L472, docstring tag [eq:tr1]

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

theorem Zeta23.PrimeSide.tr1Prime : EvBound (fun T => D.trG T - P.L T * D.Ncnt T)
    (fun T => P.calE T * (P.L T * D.Ncnt T)) := by sorry
