-- Prove2me | Theorems.Thm_WolffPASTA_Main_eq_7
-- name    : WolffPASTA.Main.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:01.168128+00:00
-- url     : https://prove2.me/theorems/bf40e27a-2abd-4963-a25c-1ed48ef5ec99
-- title:
--   (7), p. 227 — E{R²(t)} ≤ E{A²(t)} + λ²t² = λt + 2λ²t²
-- statement:
--   Let $A$ be a Poisson process at rate $\lambda>0$ on a probability space $(\Omega,\mathcal F,P)$, and let $U$ be any process with values $0\le U(s)\le1$ for $s\ge0$. Define $V(t)=t^{-1}\int_0^tU(s)\,ds$, $Y(t)=\int_0^tU(s)\,dA(s)$ and $R(t)=Y(t)-\lambda tV(t)$. Then for every $t\ge0$
--
--   $$E\{R^2(t)\}\le\lambda t+2\lambda^2t^2\equiv k(t).$$
--
--   The bound follows from $0\le Y(t)\le A(t)$, $0\le V(t)\le1$ and $E\{A^2(t)\}=\lambda t+\lambda^2t^2$; it is the second-moment estimate behind the strong law of Lemma 2.
--
--   **Formalization Note** The page's $U$ is an indicator; the statement is made for any process with values in $[0,1]$, which is all the bound uses, and without LAA or path conditions. The expectation of $R^2(t)$ is a lower Lebesgue integral in $[0,\infty]$, so it is meaningful even before $R(t)$ is known to be square integrable.
-- source:
--   Wolff, Poisson Arrivals See Time Averages, Oper. Res. 30 (1982), DOI 10.1287/opre.30.2.223, p. 227, display (7) in the proof of LEMMA 2

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace WolffPASTA.Main

/-- Display (7), p. 227: `E{R²(t)} ≤ E{A²(t)} + λ²t² = λt + 2λ²t²`, for any process `U` with values
in `[0, 1]`. -/
theorem eq_7
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam)
    (U : ℝ → Ω → ℝ) (hU : ∀ s ω, 0 ≤ s → 0 ≤ U s ω ∧ U s ω ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (R U A lam t ω ^ 2) ∂P ≤
      ENNReal.ofReal (lam * t + 2 * lam ^ 2 * t ^ 2) := by sorry

end WolffPASTA.Main
