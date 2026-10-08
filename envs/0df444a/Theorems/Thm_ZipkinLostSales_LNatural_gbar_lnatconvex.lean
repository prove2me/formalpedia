-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_gbar_lnatconvex
-- name    : ZipkinLostSales.LNatural.gbar_lnatconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:01.02501+00:00
-- url     : https://prove2.me/theorems/a245917b-60e4-4c50-98e4-3cf806347591
-- title:
--   Proof of Theorem 4, p. 939 — if f̄_{t+1} is L♮-convex, so is ḡ_t(v, ζ) of (5)
-- statement:
--   Consider the lost-sales model with lead time $L\ge1$, nonnegative independent demands with common law $\mu$ of finite mean, nonnegative unit costs $c,\hat h,p$ and discount factor $0<\gamma\le1$. Let $\bar f_k$ and $\bar g_k$ be the optimal cost functions with $k$ periods to go in the transformed state, so that
--   $$\bar g_k(v,\zeta)=-\gamma^L c\zeta+\hat q^0(v_0-v_1)+\gamma E\big[\bar f_k(v_+)\big].$$
--   If $\bar f_k$ (the paper's $\bar f_{t+1}$) is L♮-convex on $V$, then $\bar g_k$ (the paper's $\bar g_t$) is L♮-convex on $V\times\Re^-$.
--
--   In the paper this is the step $\bar g_t(v,\zeta)=-\gamma^Lc\zeta+E_d[\bar\kappa_t(v,\zeta\mid d)]$ of (5), with L♮-convexity preserved by expectation; together with Lemma 2 it closes the induction of Theorem 4.
--
--   **Formalization Note.** $\bar g_k$ is defined by the recursion (1) in the transformed state, not by (5); the two agree by the reformulation milestone (optimal $a=\min\{d,v_0-v_1\}$). Time is the number of periods to go. The cost hypotheses read "unit cost" and "discount rate"; finite mean demand is added so that $\hat q^0$ is finite. Expectations are Bochner integrals against $\mu$.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), proof of Theorem 4, display (5) and "L♮-convexity is preserved by expectation, therefore ḡ_t is L♮-convex"

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): if `f̄_{t+1}` (here `fbar … k`) is L♮-convex on `V`,
then `ḡ_t(v, ζ) = −γ^L c ζ + E_d[κ̄_t(v, ζ | d)]` (here `gbar … k`) is L♮-convex on `V × ℜ⁻`. -/
theorem gbar_lnatconvex (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (k : ℕ) (hk : LNatConvexOn (V L) (fbar c hh p γ μ k)) :
    LNatConvexOn (VxNeg L) (liftG (gbar c hh p γ μ k)) := by sorry

end ZipkinLostSales.LNatural
