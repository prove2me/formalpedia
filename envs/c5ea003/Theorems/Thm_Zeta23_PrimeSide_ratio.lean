-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_ratio
-- name    : Zeta23.PrimeSide.ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:37:55.524287+00:00
-- url     : https://prove2.me/theorems/3b9e32c9-6218-44fd-ab62-ee1a725b2c6d
-- title:
--   The trace ratio: $(\operatorname{tr}\tilde{G})^2/\operatorname{tr}\tilde{G}^2 = F(\lambda_1)\, N(T,2T)\, (1 + O(\mathcal{E}_T))$ ([eq:ratio])
-- statement:
--   **Setup.** This is stated in the abstract [thm:traces] assembly of `Zeta23.PrimeSideB`: $P$ is a parameter triple $(\varrho, \lambda, w)$ with derived $L = \lambda l$, $l = \log(T/2\pi)$, $\ell_1 = l + 2\log 2 - 1$, $\lambda_1 = L/\ell_1$; $D$ is an abstract data record whose fields $\operatorname{tr}\tilde{G} = $ `D.trG`, $\operatorname{tr}\tilde{G}^2 = $ `D.trG2`, and $N = $ `D.Ncnt` are real functions of $T$ (in the concrete instantiation, the prime-side traces and the zero count $N(T,2T)$); the ambient hypothesis is `Facts D`, the record collecting the conclusions of all §5 sub-results ([prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross], [eq:RvM], [eq:muints], [eq:abdef]). Further, $F(x) = x/(1 + x^2/3)$ [eq:Fdef], and $\mathcal{E}_T = w/L + (l^2 + X)\log l/(T l) + T^{\lambda/2 - 1}$ is the error scale of [thm:traces]. `EvBound f g` means: $\exists\, C > 0$ and $T_0$ with $|f(T)| \le C\, g(T)$ for all $T \ge T_0$.
--
--   **Statement.** Under `Facts D`,
--   $$\left|\frac{\bigl(\operatorname{tr}\tilde{G}(T)\bigr)^2}{\operatorname{tr}\tilde{G}^2(T)} - F(\lambda_1)\, N(T,2T)\right| \le C \cdot \mathcal{E}_T \cdot F(\lambda_1)\, N(T,2T)$$
--   eventually — i.e. $(\operatorname{tr}\tilde{G})^2/\operatorname{tr}\tilde{G}^2 = F(\lambda_1)\, N(T,2T)\,(1 + O(\mathcal{E}_T))$, which is [eq:ratio]. (Division here is real division; the hypotheses make $\operatorname{tr}\tilde{G}^2 > 0$ eventually.)
--
--   **Role.** The culminating ratio bound of the prime side: combined through `Zeta23.PrimeSide.tracesBounds_of_facts` into the `TracesBounds` record, it is the quantity compared against the zero-side variational lower bound to yield the $2/3$ proportion of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L774-L805, docstring tag [eq:ratio]

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

theorem Zeta23.PrimeSide.ratio : EvBound (fun T => D.trG T ^ 2 / D.trG2 T - Ffun (P.lam1 T) * D.Ncnt T)
    (fun T => P.calE T * (Ffun (P.lam1 T) * D.Ncnt T)) := by sorry
