-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_lemma_2
-- name    : ZipkinLostSales.LNatural.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:32.121986+00:00
-- url     : https://prove2.me/theorems/7c651ef6-fa0f-49a6-adf5-ee40615b6df7
-- title:
--   Lemma 2, p. 939 — if g(v, ζ) is L♮-convex, so is f(v) = min_{ζ≤0} g(v, ζ)
-- statement:
--   Let $L\ge1$, let $V\subseteq\mathbb R^L$ be the cone of nonnegative vectors with nonincreasing components, and let $g:V\times\Re^-\to\mathbb R$.
--
--   If $g$ is L♮-convex on $V\times\Re^-$ and, for every $v\in V$, the values $\{g(v,\zeta):\zeta\le0\}$ are bounded below, then
--   $$f(v)=\inf_{\zeta\le 0} g(v,\zeta)$$
--   is L♮-convex on $V$.
--
--   This is the step that carries L♮-convexity from $\bar g_t$ to $\bar f_t=\min_{\zeta\le0}\bar g_t$ in the proof of Theorem 4.
--
--   **Formalization Note.** The paper writes $\min_{\zeta\le0}$. The formalization takes the infimum over $\zeta\le0$ and assumes it is over a set bounded below (which holds whenever the minimum exists); without that assumption Lean's real infimum would return the junk value $0$. L♮-convexity on $V\times\Re^-$ is `LNatConvexOn (VxNeg L)` applied to $g$ viewed on `Fin (L+1) → ℝ` with $\zeta$ as the last coordinate.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 939 (PDF p. 4), Lemma 2

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Lemma 2 (Zipkin 2008, p. 939): if `g(v, ζ)` is L♮-convex on `V × ℜ⁻`, so is
`f(v) = min_{ζ ≤ 0} g(v, ζ)` on `V`. The "min" is the infimum over `ζ ≤ 0`, assumed bounded
below for every `v ∈ V`. -/
theorem lemma_2 (L : ℕ) (hL : 0 < L) (g : (Fin L → ℝ) → ℝ → ℝ)
    (hg : LNatConvexOn (VxNeg L) (liftG g))
    (hbdd : ∀ v ∈ V L, BddBelow (g v '' Set.Iic 0)) :
    LNatConvexOn (V L) (fun v => ⨅ ζ : Set.Iic (0 : ℝ), g v ζ) := by sorry

end ZipkinLostSales.LNatural
