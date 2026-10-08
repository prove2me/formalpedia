-- Prove2me | Theorems.Thm_WolffPASTA_Main_eq_11
-- name    : WolffPASTA.Main.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:03.761326+00:00
-- url     : https://prove2.me/theorems/862d4d9e-e346-401c-b00c-eb8d8809c6f7
-- title:
--   (11), p. 227 — R(nh) − λh ≤ R(t) ≤ R((n+1)h) + λh for t ∈ [nh, (n+1)h]
-- statement:
--   Let $A$ be a Poisson process at rate $\lambda>0$ on a probability space $(\Omega,\mathcal F,P)$, and let $U$ be a process with $0\le U(s)\le1$ for $s\ge0$ that is jointly measurable on $\Omega\times[0,\infty)$. With $V(t)=t^{-1}\int_0^tU(s)\,ds$, $Y(t)=\int_0^tU\,dA$ and $R(t)=Y(t)-\lambda tV(t)$, for every sample point $\omega$, every $h>0$ and every $n=0,1,2,\dots$,
--
--   $$R(nh)-\lambda h\le R(t)\le R((n+1)h)+\lambda h,\qquad t\in[nh,(n+1)h].$$
--
--   The inequality holds path by path because $Y$ is non-decreasing and $tV(t)=\int_0^tU(s)\,ds$ changes by at most $h$ on an interval of length $h$. It lets the grid strong law (10) be extended to all $t$ in Lemma 2.
--
--   **Formalization Note** The statement is made for any jointly measurable process with values in $[0,1]$ (the page's $U$ is an indicator); joint measurability makes each path integrable on bounded intervals, so $\int_0^tU(s)\,ds$ is additive in $t$. LAA and path regularity are not needed.
-- source:
--   Wolff, Poisson Arrivals See Time Averages, Oper. Res. 30 (1982), DOI 10.1287/opre.30.2.223, p. 227, display (11) in the proof of LEMMA 2

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace WolffPASTA.Main

/-- Display (11), p. 227: pathwise, `R(nh) - λh ≤ R(t) ≤ R((n + 1)h) + λh` for
`t ∈ [nh, (n + 1)h]`, for any jointly measurable process `U` with values in `[0, 1]`. -/
theorem eq_11
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (U : ℝ → Ω → ℝ) (hU : ∀ s ω, 0 ≤ s → 0 ≤ U s ω ∧ U s ω ≤ 1)
    (hjoint : JointlyMeasurable U) :
    ∀ ω, ∀ h : ℝ, 0 < h → ∀ (n : ℕ) (t : ℝ), n * h ≤ t → t ≤ (n + 1) * h →
      R U A lam (n * h) ω - lam * h ≤ R U A lam t ω ∧
        R U A lam t ω ≤ R U A lam ((n + 1) * h) ω + lam * h := by sorry

end WolffPASTA.Main
