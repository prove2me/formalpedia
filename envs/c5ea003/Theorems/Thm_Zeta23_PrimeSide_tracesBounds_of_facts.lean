-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_tracesBounds_of_facts
-- name    : Zeta23.PrimeSide.tracesBounds_of_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:38:01.186533+00:00
-- url     : https://prove2.me/theorems/ef37c402-6e5a-45ff-92e0-dc24d5656033
-- title:
--   Theorem [thm:traces]: assembly of the trace bounds on the prime side
-- statement:
--   Fix parameters $P = (\varrho, \lambda, w)$ — a taper profile $\varrho$, an exponent $\lambda$ with $0 < \lambda \le 1$, and a ramp width $w \ge 1$. For $T > 0$ write $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, $\ell_1 = l + 2\log 2 - 1$, and let $$\mathcal{E}_T \;=\; \frac{w}{L} + \frac{(l^2 + X)\log l}{T\,l} + T^{\lambda/2 - 1}$$ be the error parameter of Theorem [thm:traces]. The statement is parametric in abstract data $D$: real-valued functions of $T$ standing for the quantities of the paper's §5, among them $\operatorname{tr}\tilde G(T)$ (the trace of the normalized prime-side matrix $\tilde G = G/L$, $G_{kl} = \int_{\mathbb R} \hat\varphi(\tau - \tau_k)\hat\varphi(\tau - \tau_l)\,\nu_X(\tau)\,d\tau$, the second expression of [eq:Gdef]), $\operatorname{tr}\tilde G^2(T)$, and $N(T,2T)$ (the number of nontrivial zeros of $\zeta$ with ordinate in $(T, 2T]$, with multiplicity). `EvBound f g` is the explicit-constant big-$O$: there exist $C > 0$ and $T_0$ such that $|f(T)| \le C\,g(T)$ for all $T \ge T_0$. The theorem carries the standing hypothesis `Facts D`: the conclusions of the §5 sub-results ([prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]) together with the classical inputs [eq:RvM], [eq:muints] and the taper bounds [eq:abdef], each in `EvBound` form on the data $D$.
--
--   **Statement.** Under `Facts D`, the full conclusion of the paper's **Theorem [thm:traces]** (§5, ''Summary'') holds for the data $D$: the `Prop`-valued structure `TracesBounds P D.aT D.trG D.trG2 D.Ncnt`, whose four fields are the `EvBound` asymptotics
--
--   $$\operatorname{tr}\tilde G = a L\, N(T,2T) + O(L\sqrt X), \qquad \operatorname{tr}\tilde G = L\, N(T,2T)\bigl(1 + O(\mathcal{E}_T)\bigr), \tag{eq:tr1}$$
--
--   $$\operatorname{tr}\tilde G^2 = \frac{T L}{2\pi}\Bigl(\ell_1^2 + \frac{L^2}{3}\Bigr)\bigl(1 + O(\mathcal{E}_T)\bigr), \tag{eq:tr2}$$
--
--   $$\frac{(\operatorname{tr}\tilde G)^2}{\operatorname{tr}\tilde G^2} = F(\lambda_1)\, N(T,2T)\bigl(1 + O(\mathcal{E}_T)\bigr), \qquad F(x) = \frac{x}{1 + x^2/3},\ \ \lambda_1 = \frac{L}{\ell_1}. \tag{eq:ratio}$$
--
--   Here $a(T)$ is the taper constant $a = L^{-1}\int\varphi^2$ of [eq:abdef], and each $O(\cdot)$ is an explicit `EvBound` (a constant $C > 0$ and threshold $T_0$, both allowed to depend on $P$).
--
--   **Role.** This is the capstone of the prime-side development (`Zeta23.PrimeSideA` + `Zeta23.PrimeSideB`, §5 of the paper): it gathers `tr1`, `tr1'`, `tr2` and `ratio` into one structure. It is consumed by the headline assemblies `Zeta23.thmA3` and `Zeta23.thmA3_cumulative`, where the trace bounds meet the zero-side matrix-variational argument to yield Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L807-L813, docstring tag [thm:traces]

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

theorem Zeta23.PrimeSide.tracesBounds_of_facts : TracesBounds P D.aT D.trG D.trG2 D.Ncnt := by sorry
