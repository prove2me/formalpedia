-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_evBound_of_eventuallyAt
-- name    : Zeta23.PrimeSide.evBound_of_eventuallyAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:23:53.730339+00:00
-- url     : https://prove2.me/theorems/196f2d98-fc42-448c-92ac-45012c2ceb42
-- title:
--   Bridge from uniform abstract bounds to explicit big-$O$ in $T$
-- statement:
--   Let $P = (\varrho, \lambda, w)$ be a fixed parameter triple. For each height $T$, $P.\mathrm{toSetting}\, T$ is the abstract setting $(T, \lambda, w)$ and $P.\mathrm{localFun}\, T$ the concrete taper datum $(\hat\varphi|_{\mathbb{R}}, \Phi|_{\mathbb{R}}, A_\varphi, g, a, b)$ at height $T$. Three interface predicates are involved: `LocalHypsEventually` says the taper facts `LocalHyps` hold for this concrete data for all $T \ge$ some threshold; `EventuallyAt` $c_\varrho\, \lambda\, Q$ says there is a $T_0$ such that $Q\, p\, F$ holds for every abstract setting $p$ with bandwidth ratio $\lambda$ and $T \ge T_0$ and every $F$ satisfying `LocalHyps`; and `EvBound` $f\, g$ is the explicit-constant big-$O$ shape $\exists C > 0,\ \exists T_0,\ \forall T \ge T_0,\ |f(T)| \le C\, g(T)$.
--
--   The theorem is the generic specialization bridge: given `LocalHypsEventually`, if for some constant $C$ the bound $|f\, p\, F| \le C \cdot g\, p\, F$ holds in `EventuallyAt` form for abstract functionals $f, g : \mathrm{Setting} \to \mathrm{LocalFun} \to \mathbb{R}$, and if the majorant $g(P.\mathrm{toSetting}\, T)(P.\mathrm{localFun}\, T)$ is nonnegative for all large $T$, then
--   $$\mathrm{EvBound}\ \bigl(T \mapsto f(P.\mathrm{toSetting}\, T)(P.\mathrm{localFun}\, T)\bigr)\ \bigl(T \mapsto g(P.\mathrm{toSetting}\, T)(P.\mathrm{localFun}\, T)\bigr).$$
--   In words: a uniform abstract-layer estimate, once the concrete tapers are known to satisfy the local hypotheses eventually, becomes an explicit big-$O$ statement in the single variable $T$.
--
--   It is the routine plumbing by which each Section 5 sub-result enters `concreteFacts`, the bundle of [thm:traces] hypotheses for the concrete data (module `Zeta23.PrimeSideB.Concrete`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/Concrete.lean#L79-L98

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
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideTemp

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (P : Params) (T : ℝ)
variable {P}

theorem Zeta23.PrimeSide.evBound_of_eventuallyAt {cϱ : ℝ} (hLoc : LocalHypsEventually cϱ P)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAt cϱ P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (P.localFun T)) :
    EvBound (fun T => f (P.toSetting T) (P.localFun T))
      (fun T => g (P.toSetting T) (P.localFun T)) := by sorry
