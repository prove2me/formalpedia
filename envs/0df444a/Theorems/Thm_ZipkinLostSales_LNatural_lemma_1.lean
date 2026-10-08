-- Prove2me | Theorems.Thm_ZipkinLostSales_LNatural_lemma_1
-- name    : ZipkinLostSales.LNatural.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:00:40.325983+00:00
-- url     : https://prove2.me/theorems/651fcd56-bba4-4e16-96f3-e453bbb0ab1b
-- title:
--   Lemma 1, p. 938 — if f(v) is L♮-convex, so is ψ(v, ζ) = f(v − ζe)
-- statement:
--   Let $L\ge1$ and let $V\subseteq\mathbb R^L$ be the cone of nonnegative vectors with nonincreasing components. Let $e$ denote the all-ones vector.
--
--   If $f:V\to\mathbb R$ is L♮-convex, then the function
--   $$\psi(v,\zeta)=f(v-\zeta e),\qquad v\in V,\ \zeta\le 0,$$
--   is L♮-convex on $V\times\Re^-$, that is, $(v,\zeta,\xi)\mapsto\psi\big((v,\zeta)-\xi(e,1)\big)$ is submodular on the set of $(v,\zeta,\xi)$ with $v\in V$ and $\zeta\le\xi\le0$.
--
--   The lemma lets L♮-convexity pass from the next period's cost $\bar f_{t+1}$ to functions of the state and the order, as in the proof of Theorem 4.
--
--   **Formalization Note.** L♮-convexity is `LNatConvexOn` of the mission's definitions file: on $V$ it is the paper's definition (submodularity of $f(v-\zeta e)$ on $V\times\Re^-$), and on $V\times\Re^-$ the shift $\xi$ acts on all $L+1$ coordinates, so the domain is $\{\zeta\le\xi\le0\}$ (the set used in the proof of Lemma 2). Functions are total on $\mathbb R^L$, but only their values on $V$ enter.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), p. 938 (PDF p. 3), Lemma 1; proof on p. 939

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model
open MeasureTheory

namespace ZipkinLostSales.LNatural

/-- Lemma 1 (Zipkin 2008, p. 938): if `f(v)` is L♮-convex on `V`, so is
`ψ(v, ζ) = f(v − ζe)` on `V × ℜ⁻`. -/
theorem lemma_1 (L : ℕ) (hL : 0 < L) (f : (Fin L → ℝ) → ℝ) (hf : LNatConvexOn (V L) f) :
    LNatConvexOn (VxNeg L) (liftG (fun v ζ => f (fun i => v i - ζ))) := by sorry

end ZipkinLostSales.LNatural
