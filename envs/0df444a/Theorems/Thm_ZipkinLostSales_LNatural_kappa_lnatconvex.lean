-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_kappa_lnatconvex
-- name    : ZipkinLostSales.LNatural.kappa_lnatconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:04.884118+00:00
-- url     : https://prove2.me/theorems/e6c03a24-d8a4-489d-94ab-5191e8ace1bb
-- title:
--   Proof of Theorem 4, p. 939 — the end-of-period cost κ̄_t(v, ζ | d) is L♮-convex
-- statement:
--   Let $L\ge1$, $\hat h,p\ge0$, $0<\gamma\le1$, $d\ge0$, and let $F:V\to\mathbb R$ be L♮-convex and nonnegative on $V$ (standing for $\bar f_{t+1}$). Define, for $v\in V$ and $\zeta\le0$,
--   $$\bar\kappa_t(v,\zeta\mid d)=\inf\Big\{\hat h(v_+-v_1)+p(v_+-v_0+d)+\gamma F\big[(v_+,v_2,\dots,v_{L-1},0)-\zeta e\big] : -d\le v_+-v_0\le0,\ v_+-v_1\ge0\Big\},$$
--   which is program (4). Then $(v,\zeta)\mapsto\bar\kappa_t(v,\zeta\mid d)$ is L♮-convex on $V\times\Re^-$.
--
--   This is the end-of-period half of the induction step of Theorem 4; the expectation over $d$ then gives $\bar g_t$.
--
--   **Formalization Note.** The paper writes $\min_{v_+}$; the formalization takes the infimum over the interval $\max(v_0-d,v_1)\le v_+\le v_0$, which is nonempty for $v\in V$, $d\ge0$. The hypothesis $F\ge0$ on $V$ (true for the model's $\bar f_{t+1}$) keeps the infimum over a set bounded below. L♮-convexity on $V\times\Re^-$ is `LNatConvexOn (VxNeg L)` with $\zeta$ as the last coordinate, the shift acting on all $L+1$ coordinates.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), proof of Theorem 4, "an argument like that of Lemma 2 shows that κ̄_t is L♮-convex"

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): if the continuation `F` (standing for `f̄_{t+1}`) is
L♮-convex and nonnegative on `V`, then for each demand value `d ≥ 0` the end-of-period cost
`κ̄(v, ζ | d)` of (4) is L♮-convex on `V × ℜ⁻`. -/
theorem kappa_lnatconvex (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (hF0 : ∀ v ∈ V L, 0 ≤ F v) (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (VxNeg L) (liftG (kappa hh p γ F d)) := by sorry

end ZipkinLostSales.LNatural
