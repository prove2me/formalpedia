-- Prove2me | Theorems.Thm_WolffPASTA_Main_eq_3
-- name    : WolffPASTA.Main.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:54.11851+00:00
-- url     : https://prove2.me/theorems/fe2c5e0c-e63f-41c5-ab82-35f2282d135b
-- title:
--   (3), p. 226 — E{Y(t)} = λtE{V(t)} = λE{∫₀ᵗ U(s)ds} under LAA
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; $N=\{N(t),t\ge0\}$ is a process with values in a measurable space $S$; $A=\{A(t),t\ge0\}$ is a Poisson process at rate $\lambda>0$; $B\subseteq S$ is a set with $\{N(t)\in B\}\in\mathcal F$ for every $t\ge0$; $U(t)=\mathbf 1\{N(t)\in B\}$; the sample paths of $U$ are left continuous with right-hand limits w.p. 1; $U$ is jointly measurable on $\Omega\times[0,\infty)$; and the Lack of Anticipation Assumption (LAA) holds: for each $t\ge0$, $\{A(t+u)-A(t),u\ge0\}$ and $\{U(s),0\le s\le t\}$ are independent.
--
--   For every $t\ge0$ the number $Y(t)=\int_0^tU(s)\,dA(s)$ of arrivals in $(0,t]$ who find $N$ in $B$ is integrable, and
--
--   $$E\{Y(t)\}=\lambda\,E\Big\{\int_0^tU(s)\,ds\Big\},$$
--
--   and for $t>0$ this also equals $\lambda t\,E\{V(t)\}$, where $V(t)=t^-1\int_0^tU(s)\,ds$.
--
--   In words: on any finite interval, the expected number of arrivals who find the system in $B$ equals the arrival rate times the expected time the system spends in $B$. It is the expected-value form of PASTA, and the starting point of the martingale argument for Theorem 1.
--
--   **Formalization Note** Integrability of $Y(t)$ is part of the conclusion, so the identity cannot hold through Lean's convention that a non-integrable function has integral $0$.
-- source:
--   Wolff, Poisson Arrivals See Time Averages, Oper. Res. 30 (1982), DOI 10.1287/opre.30.2.223, p. 226, display (3)

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace WolffPASTA.Main

/-- Display (3), p. 226: `E{Y(t)} = λ t E{V(t)} = λ E{∫₀ᵗ U(s) ds}`. -/
theorem eq_3
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hpath : PathRegular P (U N B))
    (hjoint : JointlyMeasurable (U N B))
    (hLAA : LAA P A (U N B)) :
    (∀ t, 0 ≤ t → Integrable (Y (U N B) A t) P ∧
      ∫ ω, Y (U N B) A t ω ∂P = lam * ∫ ω, (∫ s in (0 : ℝ)..t, U N B s ω) ∂P) ∧
    (∀ t, 0 < t → ∫ ω, Y (U N B) A t ω ∂P = lam * t * ∫ ω, V (U N B) t ω ∂P) := by sorry

end WolffPASTA.Main
