-- Prove2me | Theorems.Thm_ZetaBounds_neg_logDeriv_zeta_le
-- name    : ZetaBounds.neg_logDeriv_zeta_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:08:08.701274+00:00
-- url     : https://prove2.me/theorems/895d58be-08ae-4db9-8274-9492845b213b
-- title:
--   A bound for $-\zeta'/\zeta$ near the one-line
-- statement:
--   **The logarithmic derivative of $\zeta$ just to the right of the one-line.**
--
--   For a real $\sigma$ with $1 < \sigma \le 2$,
--
--   $$\Re\left(\frac{-\zeta'(\sigma)}{\zeta(\sigma)}\right) \;\le\; \frac{1}{\sigma-1} \;+\; 1.$$
--
--   As $\sigma \downarrow 1$ the left-hand side blows up, and the content of the bound is that it
--   blows up *no faster than the pole allows*: $\zeta$ has a simple pole at $s = 1$ with residue
--   $1$, so $-\zeta'/\zeta$ behaves like $1/(\sigma-1)$ there, and the theorem says the remaining
--   contribution is bounded by the absolute constant $1$ on the whole interval $(1,2]$.
--
--   Equivalently, in terms of the von Mangoldt function, for $\sigma > 1$ one has
--   $-\zeta'(\sigma)/\zeta(\sigma) = \sum_{n\ge1}\Lambda(n)n^{-\sigma}$, and the statement is the
--   explicit upper bound $\sum_n \Lambda(n)n^{-\sigma} \le \tfrac{1}{\sigma-1} + 1$.
--
--   This is one of the three standard inputs to the classical zero-free region: paired with the
--   positivity inequality $3 + 4\cos\theta + \cos 2\theta \ge 0$ and a bound on
--   $-\zeta'/\zeta$ near a hypothetical zero, it is the term that supplies the pole's contribution
--   $\tfrac{3}{\sigma-1}$ in the three-four-one argument. The restriction $\sigma \le 2$ costs
--   nothing, since for $\sigma > 2$ the quantity is bounded outright.
--
--   **Formalization note.** $\sigma$ is real and coerced into $\mathbb{C}$; the real part is taken
--   because the quotient is formally a complex number, though for real $\sigma > 1$ it is real.
-- source:
--   Classical; see Davenport, *Multiplicative Number Theory*, §13, and Titchmarsh, *The Theory of the Riemann Zeta-Function*, §3.10. Lean proof extracted from `Salt/SW/ZetaPole.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ZetaBounds

theorem neg_logDeriv_zeta_le {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-deriv riemannZeta σ / riemannZeta σ).re ≤ 1 / (σ - 1) + 1 := by sorry

end ZetaBounds
