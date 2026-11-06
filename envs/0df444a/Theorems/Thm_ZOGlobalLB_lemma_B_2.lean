-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_B_2
-- name    : ZOGlobalLB.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:48:34.638966+00:00
-- url     : https://prove2.me/theorems/42cf14aa-0ce1-4d69-8151-fd521cc26855
-- title:
--   Lemma B.2 — base-chain regularity and stationary localization
-- statement:
--   Let $T\ge1$ and let $U$ be an orthonormal frame in $\mathbb R^r$. The base objective $F_{\mathrm{base}}(z)=P(z)+B_T(U^\top y(z))$ is $C^2$, bounded below, and satisfies
--   $$F_{\mathrm{base}}(0)-\inf F_{\mathrm{base}}\le12T,\qquad\|\nabla F_{\mathrm{base}}\|\le37\sqrt T,\qquad\|\nabla^2F_{\mathrm{base}}\|\le161,$$
--   $$\|\nabla F_{\mathrm{base}}(z)\|\le1/5\ \Longrightarrow\ w_i>1\ \text{ for every } i,\quad w=U^\top y(z).$$
--
--   This all-space localization says that a small-gradient point of the base chain must have crossed the threshold $1$ in every hidden coordinate, wherever it lies.
--
--   Differences from the source:
--   - reading: ∇²F_base and inf F_base in (61) → conclusions ContDiff ℝ 2 and BddBelow added; reason: the bounds presuppose a C² function bounded below; the proof (pp.39–40) establishes both
--   - encoding: Hessian norm → norm of iteratedFDeriv ℝ 2; reason: same quantity
--   - encoding: coordinates w_i, i = 1,…,T → 0-based Fin T; reason: Lean convention
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma B.2, p.38, (61)

import Mathlib
import Definitions.Def_ZOGlobalLB_Fnew

open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-- **Lemma B.2 (Base-chain regularity and stationary localization).** Xia, Yuan,
arXiv:2610.19652, Lemma B.2, p.38, (61).

Let `1 ≤ T` and let `U = (u_1, …, u_T)` be orthonormal in `ℝʳ`. The base objective
`F_base(z) = P(z) + B_T(Uᵀ y(z))` of (18) satisfies
`F_base(0) - inf F_base ≤ 12T, ‖∇F_base‖ ≤ 37√T, ‖∇²F_base‖ ≤ 161`, and
`‖∇F_base(z)‖ ≤ 1/5 ⟹ w_i > 1` for every `i`, where `w = Uᵀ y(z)`.

**Formalization Note.** The infimum is the real `⨅`; the conclusion also states that `F_base` is
bounded below (so the infimum is the true one) and `C²` (so `∇²F_base` is the genuine Hessian,
whose norm is that of `iteratedFDeriv ℝ 2`). The standing assumptions of Appendix B (p.36) are
`1 ≤ T ≤ r` and an orthonormal frame `U`; `T ≤ r` follows from orthonormality. -/
theorem lemma_B_2 {r T : ℕ} (hT : 1 ≤ T) (U : Fin T → E r) (hU : Orthonormal ℝ U) :
    ContDiff ℝ 2 (Fbase U) ∧
    BddBelow (Set.range (Fbase U)) ∧
    Fbase U 0 - ⨅ z, Fbase U z ≤ 12 * T ∧
    (∀ z, ‖gradient (Fbase U) z‖ ≤ 37 * Real.sqrt T) ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 (Fbase U) z‖ ≤ 161) ∧
    ∀ z, ‖gradient (Fbase U) z‖ ≤ 1 / 5 → ∀ i, 1 < wcoord U z i := by sorry

end ZOGlobalLB
