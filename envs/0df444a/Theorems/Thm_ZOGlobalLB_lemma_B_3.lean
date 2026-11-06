-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_B_3
-- name    : ZOGlobalLB.lemma_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:48:27.726355+00:00
-- url     : https://prove2.me/theorems/90475cae-d64d-403a-8a9c-c450c7aa0d5f
-- title:
--   Lemma B.3 — global geometry and stationary localization of $F_{\mathrm{new}}$
-- statement:
--   Let $T\ge1$ and let $U$, $V$ be orthonormal frames. The function $F_{\mathrm{new}}$ of (24) is globally $C^2$ and coercive, $F_{\mathrm{new}}$ and $F_{\mathrm{base}}$ are bounded below, and
--   $$\inf F_{\mathrm{new}}=\inf F_{\mathrm{base}},\qquad F_{\mathrm{new}}(0,0)-\inf F_{\mathrm{new}}\le12T,$$
--   $$\|\nabla F_{\mathrm{new}}\|\le37\sqrt T+9147,\qquad\|\nabla^2F_{\mathrm{new}}\|\le H_*=\frac{66243245}{8}.$$
--   With $e_*=1/4805$, whenever $0<e_0\le e_*$,
--   $$\|\nabla F_{\mathrm{new}}(z,x)\|\le e_0\ \Longrightarrow\ w_i>1\ (\forall i),\quad\Bigl\|x-A\sum_iv_i\Bigr\|\le\frac{e_0}{\sqrt{16-e_0^2}},\quad\|P_{U^\perp}y(z)\|\le5e_0 .$$
--
--   This certificate turns every approximately stationary output into a hit of the final workspace gate.
--
--   Differences from the source:
--   - reading: inf F_new, inf F_base → BddBelow of both stated as conclusions; reason: the real infima are the true ones; the proof shows both functions are bounded below
--   - encoding: (z, x) with Euclidean norm → WithLp 2 (E r × E m); reason: Euclidean product norm, as the paper
--   - encoding: coercive → Tendsto F_new (cocompact) atTop; reason: standard meaning
--   - encoding: P_{U⊥} y → y − Σ_i ⟨u_i, y⟩ u_i; reason: equal for orthonormal U
--   - reading: sentences defining J = 961 and e* = 1/4805 → e* is the constant eStar; J is not stated; reason: definitions, not claims
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma B.3, p.40, (72)–(73)

import Mathlib
import Definitions.Def_ZOGlobalLB_Fnew

open Filter
open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-- **Lemma B.3 (Global geometry and stationary localization).** Xia, Yuan, arXiv:2610.19652,
Lemma B.3, p.40, (72)–(73).

Let `1 ≤ T` and let `U` (in `ℝʳ`) and `V` (in `ℝᵐ`) be orthonormal frames. The function (24) is
globally `C²` and coercive; it satisfies `inf F_new = inf F_base`,
`F_new(0, 0) - inf F_new ≤ 12T`, `‖∇F_new‖ ≤ 37√T + 9147`, and
`‖∇²F_new‖ ≤ H* := 66243245/8`. With `e* = 1/4805`, whenever `0 < e₀ ≤ e*`,
`‖∇F_new(z, x)‖ ≤ e₀` implies `w_i > 1` for all `i`, `‖x - A Σ_i v_i‖ ≤ e₀/√(16 - e₀²)`, and
`‖P_{U⊥} y(z)‖ ≤ 5e₀` (73).

**Formalization Note.** `F_new` is a function on `WithLp 2 (E r × E m)` (Euclidean norm on pairs),
and `∇`, `∇²` are its gradient and `iteratedFDeriv ℝ 2` there. Coercive is
`Tendsto F_new (cocompact _) atTop`. Both functions are stated bounded below, so the real infima
are the true ones. `P_{U⊥} y = y - Σ_i ⟨u_i, y⟩ u_i` is the projection onto the orthogonal
complement of `span U` (written out, using orthonormality of `U`). -/
theorem lemma_B_3 {r m T : ℕ} (hT : 1 ≤ T) (U : Fin T → E r) (V : Fin T → E m)
    (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V) :
    ContDiff ℝ 2 (Fnew U V) ∧
    Tendsto (Fnew U V) (cocompact _) atTop ∧
    BddBelow (Set.range (Fnew U V)) ∧
    BddBelow (Set.range (Fbase U)) ∧
    ⨅ p, Fnew U V p = ⨅ z, Fbase U z ∧
    Fnew U V 0 - ⨅ p, Fnew U V p ≤ 12 * T ∧
    (∀ p, ‖gradient (Fnew U V) p‖ ≤ 37 * Real.sqrt T + 9147) ∧
    (∀ p, ‖iteratedFDeriv ℝ 2 (Fnew U V) p‖ ≤ Hstar) ∧
    ∀ e₀ : ℝ, 0 < e₀ → e₀ ≤ eStar → ∀ (z : E r) (x : E m),
      ‖gradient (Fnew U V) (WithLp.toLp 2 (z, x))‖ ≤ e₀ →
        (∀ i, 1 < wcoord U z i) ∧
        ‖x - Acst • ∑ i, V i‖ ≤ e₀ / Real.sqrt (16 - e₀ ^ 2) ∧
        ‖ycoord T z - ∑ i, ⟪U i, ycoord T z⟫ • U i‖ ≤ 5 * e₀ := by sorry

end ZOGlobalLB
