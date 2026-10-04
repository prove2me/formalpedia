-- Prove2me | Theorems.Thm_ZetaNine_five_sample_sign_forces_nonzero
-- name    : ZetaNine.five_sample_sign_forces_nonzero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T03:25:15.547385+00:00
-- url     : https://prove2.me/theorems/ca69bae0-6b9f-4b30-8a23-ceb6c61e402c
-- title:
--   Five-sample one-sign test forces non-vanishing
-- statement:
--   ## A five-sample one-sign test forces non-vanishing
--
--   Let $L$ be a real linear functional on $\mathbb{R}[X]$, let $y,w:\{0,1,2,3,4\}\to\mathbb{R}$
--   be five nodes and five weights, and assume
--
--   1. the five nodes are distinct ($y$ injective);
--   2. every weight is strictly positive, $w_j>0$;
--   3. $L$ agrees with the rule on the moments of degrees zero through four,
--      $L(X^m)=\sum_j w_j\,y_j^m$ for $0\le m\le 4$.
--
--   Then for every nonzero polynomial $p$ of degree at most four whose five sampled values
--   $p(y_j)$ are **weakly of one sign** — either $p(y_j)\ge0$ for all $j$, or
--   $p(y_j)\le0$ for all $j$ — one has $L(p)\ne0$.
--
--   **Why.** Hypothesis 3 is exactly the moment-matching condition of the exact quadrature
--   core, so $L(p)=\sum_j w_j\,p(y_j)$. Every summand has the sign required at its node.
--   If $L(p)$ vanished, the sum of identically signed terms would vanish, forcing every
--   summand to vanish; since $w_j\ne0$ this gives $p(y_j)=0$ at five distinct nodes. A
--   nonzero polynomial of degree at most four cannot have five distinct roots. This is
--   the point where the "no need to inspect the sign between the sampled points" claim of
--   the five-sample criterion is made precise.
--
--   **Scope.** This is the exact composition of local nodes **FQ** and **TP**: FQ supplies
--   the cubature identity, the root count supplies the exclusion of a vanishing quartic,
--   and the strict positivity of the weights converts "weak sign" into "strict
--   non-vanishing". It is stated for abstract data. It does **not** assert that the
--   weights of the actual construction are strictly positive — that is the analytic
--   Gaussian-moment input GC — and it does **not** assert that any actual moving shortest
--   output passes the five-sample test, which is the open target T5. Zero values at
--   sampled nodes are allowed, so no hypothesis excludes a single vanishing sample; what
--   is excluded is simultaneous vanishing at all five.
-- source:
--   Local zeta9 research note, roadmap/research/moving-short-sign-next.md sections 5-6 and roadmap/DAG.md node TP, 2026-09-25

import Mathlib

namespace ZetaNine

theorem five_sample_sign_forces_nonzero
    (L : Polynomial ℝ →ₗ[ℝ] ℝ) (y w : Fin 5 → ℝ)
    (hy : Function.Injective y)
    (hw : ∀ j : Fin 5, 0 < w j)
    (hmom : ∀ m : ℕ, m ≤ 4 →
      L ((Polynomial.X : Polynomial ℝ) ^ m) = ∑ j : Fin 5, w j * (y j) ^ m)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ 4) (hp : p ≠ 0)
    (hsign : (∀ j : Fin 5, 0 ≤ p.eval (y j)) ∨ (∀ j : Fin 5, p.eval (y j) ≤ 0)) :
    L p ≠ 0 := by sorry

end ZetaNine
