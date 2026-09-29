-- Prove2me | Theorems.Thm_riemannZeta_conj
-- name    : riemannZeta_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:08:03.825255+00:00
-- url     : https://prove2.me/theorems/f0bd7609-184e-4e70-843b-82611d527705
-- title:
--   Reflection symmetry of $\zeta$: $\zeta(\bar{s}) = \overline{\zeta(s)}$
-- statement:
--   For every complex number $s$, the Riemann zeta function commutes with complex conjugation:
--
--   $$\zeta(\bar{s}) \;=\; \overline{\zeta(s)}.$$
--
--   This is the Schwarz reflection property of $\zeta$, valid on all of $\mathbb{C}$ (with the completed meromorphic continuation): it holds because $\zeta$ is real on the real axis where its Dirichlet series converges, and the identity propagates to the full plane by analytic continuation.
--
--   The reflection identity halves the work in zero-free-region and growth estimates: any bound on $\zeta$ or on $|\zeta(\sigma + it)|$ established for $t \ge 0$ transfers immediately to $t \le 0$, and zeros of $\zeta$ come in conjugate pairs. The PNT+ development uses it to reduce vertical-strip estimates to the upper half-plane.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaConj.lean#L66-L67

import Mathlib.NumberTheory.LSeries.RiemannZeta

open scoped Complex ComplexConjugate

theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by sorry
