-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_optimal_fill
-- name    : ZipkinLostSales.LNatural.optimal_fill
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:47.236575+00:00
-- url     : https://prove2.me/theorems/b9cdfe61-da13-4637-a337-a8e50679ecb0
-- title:
--   Proof of Theorem 4, p. 939 — in program (3), the optimal a = min{d, v₀ − v₁}
-- statement:
--   Consider the lost-sales model with lead time $L\ge1$, nonnegative independent demands with common law $\mu$ of finite mean, nonnegative unit costs $c,\hat h,p$ and discount factor $0<\gamma\le1$. Let $\bar f_k$ be the optimal cost with $k$ periods to go in the transformed state (with $\bar f_0=0$).
--
--   After demand $d\ge 0$ is observed in a period whose continuation cost is $\bar f_{t+1}=\bar f_k$, the paper's program (3) chooses the amount $a$ of demand to fill and the remaining inventory $w$:
--   $$\bar\kappa_t(v,\zeta\mid d)=\min_{a,w}\Big\{\hat h w+p(d-a)+\gamma\bar f_{t+1}\big[(w+v_1,v_2,\dots,v_{L-1},0)-\zeta e\big] : a+w=v_0-v_1,\ 0\le a\le d,\ w\ge0\Big\}.$$
--   The claim is that the optimal $a$ is $\min\{d,v_0-v_1\}$: for every $v\in V$, $\zeta\le0$ and $d\ge 0$,
--   $$\bar\kappa_t(v,\zeta\mid d)=\hat q(v_0-v_1-d)+\gamma\,\bar f_{t+1}(v_+),\qquad v_+=\big([v_0-v_1-d]^+ +v_1,v_2,\dots,v_{L-1},0\big)-\zeta e,$$
--   where $\hat q(u)=\hat h u^+ + p u^-$.
--
--   The paper notes this "is not hard, but also not essential" for Theorem 4; it is what makes the two-step program (4)–(5) agree with the recursion (1). It depends on the model: it uses $\hat h,p\ge0$, $\gamma\le 1$ and the specific $\bar f_{t+1}$, and fails for an arbitrary continuation function.
--
--   **Formalization Note.** The program is stated in the form (4), after the substitution $v_+=w+v_1$ (so $a=\min\{d,v_0-v_1\}$ is $v_+=\max(v_0-d,v_1)$); $\bar\kappa$ is the infimum over the interval $\max(v_0-d,v_1)\le v_+\le v_0$, and the equality says the infimum equals the value at the left endpoint. Time is the number of periods to go $k$ (`fbar … k` is the paper's $\bar f_{t+1}$, for every period $t$ of every horizon). Vectors are indexed $0,\dots,L-1$ with $v_L=0$. The cost hypotheses ($c,\hat h,p\ge0$, $0<\gamma\le1$) read the paper's "unit cost" and "discount rate"; nonnegative demand is the paper's; finite mean demand is added so that $\hat q^0$ is finite.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), proof of Theorem 4, program (3) and the remark "the optimal a = min{d, v₀ − v₁}", together with the substitution leading to (4)

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): in program (3)/(4) with continuation `f̄_{t+1}`
(here `fbar … k`), filling as much demand as possible (`a = min{d, v₀ − v₁}`, i.e.
`v₊ = max(v₀ − d, v₁)`) is optimal, so `κ̄(v, ζ | d) = q̂(v₀ − v₁ − d) + γ f̄_{t+1}(v₊)` with `v₊`
the transition of p. 938. -/
theorem optimal_fill (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℕ) (v : Fin L → ℝ) (hv : v ∈ V L) (ζ : ℝ) (hζ : ζ ≤ 0) (d : ℝ) (hd : 0 ≤ d) :
    kappa hh p γ (fbar c hh p γ μ k) d v ζ =
      qhat hh p (vext v 0 - vext v 1 - d) + γ * fbar c hh p γ μ k (next v d ζ) := by sorry

end ZipkinLostSales.LNatural
