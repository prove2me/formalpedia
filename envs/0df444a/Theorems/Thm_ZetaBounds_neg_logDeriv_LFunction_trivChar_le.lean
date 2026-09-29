-- Prove2me | Theorems.Thm_ZetaBounds_neg_logDeriv_LFunction_trivChar_le
-- name    : ZetaBounds.neg_logDeriv_LFunction_trivChar_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T12:41:54.878499+00:00
-- url     : https://prove2.me/theorems/e7bd57f0-da4a-4ddb-a7fe-d43bc97d62e8
-- title:
--   A bound for $-L'/L$ of the principal character near the one-line
-- statement:
--   **The principal-character analogue of the bound for $-\zeta'/\zeta$ near the one-line.**
--
--   Let $\chi_0$ be the principal character modulo $q$. For real $\sigma$ with $1 < \sigma \le 2$,
--
--   $$\Re\left(\frac{-L'(\sigma,\chi_0)}{L(\sigma,\chi_0)}\right) \;\le\; \frac{1}{\sigma-1} \;+\; 1 .$$
--
--   The $L$-function of the principal character is $\zeta$ with the Euler factors at the primes
--   dividing $q$ removed,
--
--   $$L(s,\chi_0) \;=\; \zeta(s)\prod_{p \mid q}\left(1 - p^{-s}\right),$$
--
--   so it inherits the simple pole of $\zeta$ at $s = 1$, and the bound says its logarithmic
--   derivative blows up no faster than that pole dictates — **uniformly in the modulus $q$**, which
--   is the point: the removed Euler factors contribute
--   $\sum_{p\mid q}\tfrac{\log p}{p^{\sigma}-1} \ge 0$ with the *right* sign, so deleting them only
--   decreases $-L'/L$.
--
--   Together with the positivity inequality $3 + 4\cos\theta + \cos 2\theta \ge 0$ and a bound near
--   a hypothetical zero, this is the pole term in the three-four-one argument that produces the
--   zero-free region for Dirichlet $L$-functions, and hence the prime number theorem in arithmetic
--   progressions. Uniformity in $q$ is what makes the resulting region usable in applications such
--   as the Siegel–Walfisz theorem.
--
--   **Formalization note.** `DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)` is the
--   $L$-function of the principal character mod $q$; $\sigma$ is real, coerced into $\mathbb{C}$,
--   and `logDeriv f = deriv f / f`.
-- source:
--   Classical; see Davenport, *Multiplicative Number Theory*, §14, and Montgomery & Vaughan, *Multiplicative Number Theory I*, §11.3. Lean proof extracted from `Salt/SW/ZetaPole.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ZetaBounds

theorem neg_logDeriv_LFunction_trivChar_le (q : ℕ) [NeZero q] {σ : ℝ}
    (h1 : 1 < σ) (h2 : σ ≤ 2) :
    (-logDeriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)).re
      ≤ 1 / (σ - 1) + 1 := by sorry

end ZetaBounds
