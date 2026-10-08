-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_psi_lnatconvex
-- name    : ZipkinLostSales.LNatural.psi_lnatconvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:53.657714+00:00
-- url     : https://prove2.me/theorems/6dd2bf52-7c1d-46a0-8455-3ba34cbaa7aa
-- title:
--   Proof of Theorem 4, p. 939 — the objective ψ_t(v₊, v, ζ) of (4) is L♮-convex
-- statement:
--   Let $L\ge1$, $\hat h,p\ge0$, $0<\gamma\le1$, $d\ge0$, and let $F:V\to\mathbb R$ be L♮-convex (standing for $\bar f_{t+1}$). Consider the objective of program (4),
--   $$\psi_t(v_+,v,\zeta)=\hat h(v_+-v_1)+p(v_+-v_0+d)+\gamma F\big[(v_+,v_2,\dots,v_{L-1},0)-\zeta e\big],$$
--   on the set $D_d$ of $(v_+,v,\zeta)\in\mathbb R\times\mathbb R^L\times\mathbb R$ with
--   $$v\in V,\quad \zeta\le 0,\quad -d\le v_+-v_0\le 0,\quad v_+-v_1\ge0 .$$
--   Then $\psi_t$ is L♮-convex on $D_d$: $(x,\xi)\mapsto\psi_t(x-\xi e)$ is submodular on $\{(x,\xi): \xi\le0,\ x\in D_d,\ x-\xi e\in D_d\}$, the shift acting on all $L+2$ coordinates $(v_+,v_0,\dots,v_{L-1},\zeta)$.
--
--   In the proof of Theorem 4 this is the step before minimizing over $v_+$.
--
--   **Formalization Note.** Points of $D_d$ are encoded as `Fin (L+2) → ℝ` with coordinates ordered $(v_+,v_0,\dots,v_{L-1},\zeta)$ (`Dpsi`, `liftPsi`). The trailing $0$ in $(v_+,v_2,\dots,v_{L-1},0)$ is the convention $v_L=0$ and is not shifted. $F$ is a total function on $\mathbb R^L$ whose L♮-convexity is assumed on $V$ only; every argument of $F$ above lies in $V$. The hypotheses $\hat h,p\ge0$, $\gamma\le1$ are the paper's standing cost assumptions.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), proof of Theorem 4, program (4) and "Moreover, Lemma 1 implies that ψ_t is L♮-convex"

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Proof of Theorem 4 (Zipkin 2008, p. 939): if the continuation `F` (standing for `f̄_{t+1}`) is
L♮-convex on `V`, the objective `ψ_t(v₊, v, ζ)` of (4) is L♮-convex on its constraint set
(coordinates `(v₊, v₀, …, v_{L−1}, ζ)`). -/
theorem psi_lnatconvex (L : ℕ) (hL : 0 < L) (hh p γ : ℝ) (hhh : 0 ≤ hh) (hp : 0 ≤ p)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (F : (Fin L → ℝ) → ℝ) (hF : LNatConvexOn (V L) F)
    (d : ℝ) (hd : 0 ≤ d) :
    LNatConvexOn (Dpsi L d) (liftPsi hh p γ F d) := by sorry

end ZipkinLostSales.LNatural
