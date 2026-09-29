-- Prove2me | Theorems.Thm_beta_nat_factorial
-- name    : beta_nat_factorial
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:27:51.362887+00:00
-- url     : https://prove2.me/theorems/94d6a281-94f3-4cd5-9989-5f758baccd56
-- title:
--   Beta integral at natural arguments: $\int_0^1u^k(1-u)^j\,du=\frac{k!\,j!}{(k+j+1)!}$
-- statement:
--   **Beta function at natural arguments (real interval-integral form).** For all natural numbers $k, j$, the integral of $u^k(1-u)^j$ over $[0,1]$ equals the Beta value $B(k+1,j+1) = \dfrac{k!\,j!}{(k+j+1)!}$, i.e. $$\int_0^1 u^k (1-u)^j\,du = \frac{k!\,j!}{(k+j+1)!}.$$ Proof by induction on $k$: the base case $k=0$ is $\int_0^1 (1-u)^j\,du = 1/(j+1)$, and the inductive step is the integration-by-parts recurrence $\int_0^1 u^{k+1}(1-u)^j\,du = \frac{k+1}{j+1}\int_0^1 u^k(1-u)^{j+1}\,du$.
-- source:
--   Standard Beta-function evaluation $B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$ at integer arguments; e.g. Abramowitz & Stegun, Handbook of Mathematical Functions, 6.2.1-6.2.2. Real interval-integral form, proved by elementary induction + integration by parts.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
open scoped BigOperators

theorem beta_nat_factorial (k j : ℕ) :
    ∫ u in (0:ℝ)..1, u ^ k * (1 - u) ^ j
      = (Nat.factorial k * Nat.factorial j : ℝ) / Nat.factorial (k + j + 1) := by sorry
