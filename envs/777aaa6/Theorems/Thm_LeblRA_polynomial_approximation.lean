-- Prove2me | Theorems.Thm_LeblRA_polynomial_approximation
-- name    : LeblRA.polynomial_approximation
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T02:04:09.99218+00:00
-- url     : https://prove2.me/theorems/46da8979-2950-4166-b138-d299703219cd
-- title:
--   Theorem 11.7.1 — Uniform polynomial approximation on a compact interval
-- statement:
--   Let $a,b\in\mathbb R$. Both of the following assertions hold.
--
--   1. For every continuous function $f:[a,b]\to\mathbb C$, there is a sequence of complex-coefficient polynomials converging uniformly to $f$.
--   2. For every continuous function $f:[a,b]\to\mathbb R$, there is a sequence of real-coefficient polynomials converging uniformly to $f$.
--
--   For the corresponding scalar field $K$, the conclusion is
--   $$
--   \exists(p_n)_{n\in\mathbb N}\subseteq K[t]\quad
--   \forall\varepsilon>0\;\exists N\;\forall n\ge N\;\forall x\in[a,b],
--   \qquad |p_n(x)-f(x)|<\varepsilon.
--   $$
--
--   This is the complete real/complex polynomial-approximation statement of [Lebl’s Theorem 11.7.1](https://www.jirka.org/ra/html/sec_stoneweier.html), with the coefficient-field clause retained.
--
--   **Formalization Note.** The function is defined on the interval itself. A complex polynomial is evaluated at the complex embedding of the real argument. Arbitrary endpoints are allowed, so singleton and empty intervals are included. There is no degree bound, rate, or power-series assertion.
-- source:
--   Jiří Lebl, Basic Analysis II, Section 11.7, Theorem 11.7.1. Author-hosted HTML: https://www.jirka.org/ra/html/sec_stoneweier.html (accessed 2026-09-05). The algebra conventions are Definitions 11.7.5, 11.7.7, and 11.7.15; no unit is assumed.

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA
theorem polynomial_approximation (a b : ℝ) :
    (∀ f : C(Set.Icc a b, ℂ), ∃ p : ℕ → ℂ[X],
      TendstoUniformly (fun n (x : Set.Icc a b) => (p n).eval ((x : ℝ) : ℂ)) f atTop) ∧
    (∀ f : C(Set.Icc a b, ℝ), ∃ p : ℕ → ℝ[X],
      TendstoUniformly (fun n (x : Set.Icc a b) => (p n).eval (x : ℝ)) f atTop) := by sorry
end LeblRA
