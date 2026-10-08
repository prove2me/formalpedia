-- Prove2me | Theorems.Thm_WolffPASTA_Main_arrival_rate_limit
-- name    : WolffPASTA.Main.arrival_rate_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:56.827073+00:00
-- url     : https://prove2.me/theorems/43cb87aa-a374-48db-bba3-a4cbfafd8fe5
-- title:
--   §2, last paragraph, p. 227 — A(t)/t → λ w.p. 1 for a Poisson process at rate λ
-- statement:
--   Let $A$ be a Poisson process at rate $\lambda>0$ on a probability space $(\Omega,\mathcal F,P)$. Then
--
--   $$\frac{A(t)}{t}\to\lambda\quad\text{w.p. 1 as }t\to\infty.$$
--
--   This is the strong law of large numbers for the Poisson process. The paper's last step writes $R(t)/t=(Y(t)/A(t))(A(t)/t)-\lambda V(t)$ and combines this limit with Lemma 2 to obtain Theorem 1.
-- source:
--   Wolff, Poisson Arrivals See Time Averages, Oper. Res. 30 (1982), DOI 10.1287/opre.30.2.223, p. 227, §2, last paragraph ("Finally, Theorem 1 follows immediately from Lemma 2 and A(t)/t → λ w.p. 1")

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace WolffPASTA.Main

/-- §2, last paragraph, p. 227: for a Poisson process at rate `λ`, `A(t)/t → λ` w.p. 1. -/
theorem arrival_rate_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ → Ω → ℕ) (lam : ℝ) (hlam : 0 < lam) (hA : IsPoissonProcess P A lam) :
    ∀ᵐ ω ∂P, Tendsto (fun t => (A t ω : ℝ) / t) atTop (𝓝 lam) := by sorry

end WolffPASTA.Main
