-- Prove2me | Theorems.Thm_WolffPASTA_Main_eq_2
-- name    : WolffPASTA.Main.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:09.887393+00:00
-- url     : https://prove2.me/theorems/95ab62c2-2d8f-4f62-a807-f12126042080
-- title:
--   (2), p. 226 — E{Yₙ(t)} = λtE{Σ_{k<n} U(kt/n)/n} under LAA
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space; $N=\{N(t),t\ge0\}$ is a process with values in a measurable space $S$; $A=\{A(t),t\ge0\}$ is a Poisson process at rate $\lambda>0$; $B\subseteq S$ is a set with $\{N(t)\in B\}\in\mathcal F$ for every $t\ge0$; $U(t)=\mathbf 1\{N(t)\in B\}$; and the Lack of Anticipation Assumption (LAA) holds: for each $t\ge0$, $\{A(t+u)-A(t),u\ge0\}$ and $\{U(s),0\le s\le t\}$ are independent. (Path regularity and joint measurability are not needed here.)
--
--   For $t>0$ and $n\ge1$ let $Y_n(t)=\sum_{k=0}^{n-1}U(kt/n)\,[A((k+1)t/n)-A(kt/n)]$ be the grid approximation (1) of $Y(t)=\int_0^tU\,dA$. Then $Y_n(t)$ is integrable and
--
--   $$E\{Y_n(t)\}=\lambda t\,E\Big\{\sum_{k=0}^{n-1}U(kt/n)/n\Big\}.$$
--
--   This is display (2) of Wolff's proof of Theorem 1: under LAA each grid increment of $A$ is independent of the value of $U$ at its left endpoint. Letting $n\to\infty$ gives (3).
-- source:
--   Wolff, Poisson Arrivals See Time Averages, Oper. Res. 30 (1982), DOI 10.1287/opre.30.2.223, p. 226, display (2)

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace WolffPASTA.Main

/-- Display (2), p. 226: from LAA, `E{Yₙ(t)} = λ t E{∑_{k=0}^{n-1} U(kt/n)/n}`. -/
theorem eq_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hLAA : LAA P A (U N B))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    Integrable (Yn (U N B) A n t) P ∧
      ∫ ω, Yn (U N B) A n t ω ∂P =
        lam * t * ∫ ω, (∑ k ∈ Finset.range n, U N B (k * t / n) ω / n) ∂P := by sorry

end WolffPASTA.Main
