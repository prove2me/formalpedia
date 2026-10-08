-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_theorem_4
-- name    : ZipkinLostSales.LNatural.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:57.767251+00:00
-- url     : https://prove2.me/theorems/e9389cd4-9bb9-496f-9438-bf57cb8ac291
-- title:
--   Theorem 4, p. 939 — for all t, the lost-sales cost functions f̄_t(v) and ḡ_t(v, ζ) are L♮-convex
-- statement:
--   **Theorem 4 (Karlin and Scarf 1958 and Morton 1969).** Consider the standard single-item lost-sales inventory system in discrete time: lead time $L\ge1$; independent nonnegative demands with a common law $\mu$ of finite mean; unit procurement cost $c\ge0$, holding cost $\hat h\ge0$, lost-sales penalty $p\ge0$; discount factor $0<\gamma\le1$. In the transformed state $v\in V$ (partial sums of the pipeline, $v_l=\sum_{k\ge l}x_k$) and transformed order $\zeta=-z\le0$, let
--   $$\bar g_t(v,\zeta)=-\gamma^Lc\zeta+\hat q^0(v_0-v_1)+\gamma E\big[\bar f_{t+1}(v_+)\big],\qquad \bar f_t(v)=\min_{\zeta\le0}\bar g_t(v,\zeta),\qquad \bar f_{T+L+1}\equiv0,$$
--   with $\hat q^0(y)=E[\hat h(y-d)^+ + p(y-d)^-]$ and $v_+=([v_0-v_1-d]^+ +v_1,v_2,\dots,v_{L-1},0)-\zeta e$.
--
--   Then for all $t$, the functions $\bar f_t(v)$ and $\bar g_t(v,\zeta)$ are L♮-convex: $\bar f_t(v-\zeta e)$ is submodular in $(v,\zeta)$ on $V\times\Re^-$, and $\bar g_t\big((v,\zeta)-\xi(e,1)\big)$ is submodular in $(v,\zeta,\xi)$ for $v\in V$, $\zeta\le\xi\le0$.
--
--   L♮-convexity is the structural property from which the paper derives that the optimal order is monotone in the transformed state with limited sensitivity (Corollary 5), and from which convexity of $\bar f_t$ follows.
--
--   **Formalization Note.** Data are stationary, so $\bar f_t$ depends on $t$ only through the number of periods to go $k=T+L+1-t$; the statement is for every $k\ge0$, pairing `fbar … k` with `gbar … k` (whose continuation is `fbar … k`), which covers every $t$ of every horizon $T$. Vectors are indexed $0,\dots,L-1$ with $v_L=0$. The paper's "min" over $\zeta\le0$ is an infimum; under the hypotheses all costs are nonnegative, so it is not Lean's junk value. The cost hypotheses read the paper's "unit cost" and "discount rate"; nonnegative independent demand is the paper's, with one law because data are stationary; finite mean demand is added so that $\hat q^0$ is finite. Expectations are Bochner integrals.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), Theorem 4; model §2 (1)–(2), pp. 937–938, and §3 transformation, p. 938

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Theorem 4 (Karlin and Scarf 1958 and Morton 1969; Zipkin 2008, p. 939): for all `t`, the
functions `f̄_t(v)` and `ḡ_t(v, ζ)` are L♮-convex. With `k` the number of periods to go,
`fbar … k` is L♮-convex on `V` and `gbar … k` is L♮-convex on `V × ℜ⁻`, for every `k`. -/
theorem theorem_4 (L : ℕ) (hL : 0 < L) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (hμint : Integrable id μ)
    (c hh p γ : ℝ) (hc : 0 ≤ c) (hhh : 0 ≤ hh) (hp : 0 ≤ p) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (k : ℕ) :
    LNatConvexOn (V L) (fbar c hh p γ μ k) ∧
      LNatConvexOn (VxNeg L) (liftG (gbar c hh p γ μ k)) := by sorry

end ZipkinLostSales.LNatural
