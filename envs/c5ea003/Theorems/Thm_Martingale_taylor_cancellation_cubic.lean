-- Prove2me | Theorems.Thm_Martingale_taylor_cancellation_cubic
-- name    : Martingale.taylor_cancellation_cubic
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-15T19:10:46.052973+00:00
-- url     : https://prove2.me/theorems/137143aa-79ce-413b-a5a1-971d58394bd2
-- title:
--   The comparison is exact to second order: the Taylor polynomials differ by $ix^3/3$
-- statement:
--   An exact polynomial identity, for real $x$:
--
--   $$\Bigl(1 + ix - \tfrac{x^2}{2} - \tfrac{ix^3}{6}\Bigr) \;-\; (1 + ix)\Bigl(1 - \tfrac{x^2}{2}\Bigr) \;=\; \frac{ix^3}{3} .$$
--
--   The left factor is the third-order Taylor polynomial of $e^{ix}$; the right-hand product is $(1+ix)$ times the second-order Taylor polynomial of $e^{-x^2/2}$. **Every term of order $0$, $1$ and $2$ cancels**, and what survives is exactly cubic.
--
--   This identity is the reason McLeish's comparison works. His proof of the martingale central limit theorem replaces the characteristic function $e^{i\theta S_n}$, which cannot be factored because the summands are dependent, by $\prod_k(1 + i\theta Z_k)$, whose expectation is exactly $1$ by the martingale property. The substitution is only useful if the two agree closely enough, and this computation says precisely how closely: the discrepancy between $e^{i\theta z}$ and $(1 + i\theta z)e^{-\theta^2z^2/2}$ begins at third order in $\theta z$.
--
--   Third order is exactly what the argument needs, and second order would not do. Summing per-factor errors of size $|\theta Z_k|^3$ gives
--
--   $$\sum_{k<n} |\theta Z_k|^3 \;\le\; |\theta|^3\Bigl(\max_{k<n}|Z_k|\Bigr)\sum_{k<n} Z_k^2 \;\longrightarrow\; 0,$$
--
--   because the increments are asymptotically negligible while the sum of squares stays bounded — it converges to $\sigma^2$. Had the discrepancy been merely quadratic the bound would have been $|\theta|^2\sum_k Z_k^2 \to |\theta|^2\sigma^2 \ne 0$ and nothing would vanish. So the exact cancellation through second order recorded here is what makes the whole method work, and it explains why $1 + i\theta z$, rather than any other first-order approximation to $e^{i\theta z}$, is the right comparison factor: it is the one whose product with the Gaussian factor matches $e^{i\theta z}$ to second order.
-- source:
--   B. M. Brown, "Martingale Central Limit Theorems", Annals of Mathematical Statistics 42 (1971) 59-66, Theorem 2; D. L. McLeish, "Dependent Central Limit Theorems and Invariance Principles", Annals of Probability 2 (1974) 620-628, Theorem 2.3; P. Hall and C. C. Heyde, Martingale Limit Theory and Its Application, Academic Press 1980, Theorem 3.2 (the second-order expansion in the proof).

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Finset

theorem Martingale.taylor_cancellation_cubic (x : ℝ) :
    (1 + Complex.I * x - (x:ℂ)^2/2 - Complex.I * (x:ℂ)^3/6)
      - (1 + Complex.I * x) * (1 - (x:ℂ)^2/2)
    = Complex.I * (x:ℂ)^3 / 3 := by sorry
