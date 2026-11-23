-- Prove2me | Theorems.Thm_WolffPASTA_Main_Supplement_eq_12
-- name    : WolffPASTA.Main.Supplement.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:45:44.710877+00:00
-- url     : https://prove2.me/theorems/2a80e8bd-ff54-45d4-8837-093ebc47ca93
-- title:
--   (12), p. 228 — E{Y(t)} = ∫₀ᵗ E{U(s)}λ(s)ds for nonstationary Poisson arrivals
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space; $N$ a process with values in a measurable space; $A$ a Poisson process with intensity $\lambda(t)$, where $\lambda(t)\ge0$ is bounded and integrable on $[0,t]$ for every $t$ and $t^{-1}\Lambda(t)\to\bar\lambda$ with $0<\bar\lambda<\infty$, $\Lambda(t)=\int_0^t\lambda(s)\,ds$; $B$ a set with $\{N(t)\in B\}$ measurable for every $t\ge0$; $U(t)=\mathbf 1\{N(t)\in B\}$ with paths left continuous with right-hand limits w.p. 1 and jointly measurable on $\Omega\times[0,\infty)$; and LAA. Then for every $t\ge0$, $Y(t)=\int_0^tU(s)\,dA(s)$ is integrable and
--
--   $$E\{Y(t)\}=\int_0^tE\{U(s)\}\,\lambda(s)\,ds.$$
--
--   This is the analogue of (3) for nonstationary Poisson arrivals, and the first step of the proof of Theorem 2.
-- source:
--   Wolff, Poisson Arrivals See Time Averages, Oper. Res. 30 (1982), DOI 10.1287/opre.30.2.223, p. 228, display (12)

import Mathlib
import Definitions.Def_WolffPASTA_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace WolffPASTA.Main.Supplement

/-- Display (12), p. 228: `E{Y(t)} = ∫₀ᵗ E{U(s)} λ(s) ds` for a Poisson process with rate `λ(t)`. -/
theorem eq_12
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {S : Type*} [MeasurableSpace S] (N : ℝ → Ω → S)
    (A : ℝ → Ω → ℕ) (rate : ℝ → ℝ) (hA : IsPoissonProcessWithIntensity P A rate)
    (hrate_nonneg : ∀ s, 0 ≤ s → 0 ≤ rate s)
    (hrate_bdd : ∃ C : ℝ, ∀ s, 0 ≤ s → rate s ≤ C)
    (hrate_int : ∀ t, 0 ≤ t → IntervalIntegrable rate volume 0 t)
    (lbar : ℝ) (hlbar : 0 < lbar) (hlim : Tendsto (fun t => Lambda rate t / t) atTop (𝓝 lbar))
    (B : Set S) (hB : ∀ t, 0 ≤ t → MeasurableSet {ω | N t ω ∈ B})
    (hpath : PathRegular P (U N B))
    (hjoint : JointlyMeasurable (U N B))
    (hLAA : LAA P A (U N B))
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (Y (U N B) A t) P ∧
      ∫ ω, Y (U N B) A t ω ∂P = ∫ s in (0 : ℝ)..t, (∫ ω, U N B s ω ∂P) * rate s := by sorry

end WolffPASTA.Main.Supplement
