-- Prove2me | Theorems.Thm_unrestricted_large_sieve_hypothesis_is_false
-- name    : unrestricted_large_sieve_hypothesis_is_false
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-10-03T17:25:44.827923+00:00
-- url     : https://prove2.me/theorems/ee0cedbf-8f9e-4531-b9a7-c5141e8c5373
-- title:
--   The large sieve hypothesis with unrestricted singleton separation is false
-- statement:
--   Let $e(t)=\exp(2\pi i t)$. Consider a square-summable sequence $(a_n)_{n\in\mathbb Z}$ of complex numbers, a finite set $T\subset\mathbb Z$, a function $\xi:\mathbb Z\to\mathbb R$, and real numbers $d,u,v$ with $d>0$ and $v-u\ge1$. Suppose distinct frequencies indexed by $T$ are separated modulo the integers by at least $d$.
--
--   Under these hypotheses, the estimate
--
--   $$\sum_{r\in T}\left|\sum_{u<n\le v}a_n e(\xi(r)n)\right|^2\le\left(v-u+\frac1d\right)\sum_{n\in\mathbb Z}|a_n|^2$$
--
--   is not valid uniformly. The theorem asserts the negation of this universal claim when no upper bound on $d$ is imposed.
--
--   This diagnoses the unrestricted large-sieve hypothesis used in the existing conditional bilinear theorem. The conditional theorem remains logically valid; this result does not refute Tao's published theorem.
--
--   **Formalization Note** Separation modulo the integers is represented by the absolute difference between a real number and its nearest integer.
-- source:
--   Formalization diagnostic of hypothesis hLS in the Prove2Me theorem TaoFivePrimes.large_sieve_bilinear (theorem f7db0006-98a2-4302-8d15-2b066284aae5). The phase function is expanded from the canonical definition TaoFivePrimes.eR in TaoFivePrimes_Explicit (definition d5e52ba6-b02a-4445-9648-ff0745d31e0f). This diagnostic concerns the formal hypothesis and does not claim to refute the conditional theorem or Tao's published result.

import Mathlib

theorem unrestricted_large_sieve_hypothesis_is_false :
    ¬ (∀ (a' : ℤ → ℂ), Summable (fun n : ℤ => ‖a' n‖ ^ 2) →
        ∀ (T : Finset ℤ) (xi : ℤ → ℝ) (d u v : ℝ), 0 < d → 1 ≤ v - u →
        (∀ i ∈ T, ∀ j ∈ T, i ≠ j →
          d ≤ |(xi i - xi j) - round (xi i - xi j)|) →
        (∑ i ∈ T, ‖∑ n ∈ Finset.Ioc ⌊u⌋ ⌊v⌋, a' n * Complex.exp (2 * Real.pi * Complex.I * ((xi i * (n : ℝ)) : ℝ))‖ ^ 2)
          ≤ ((v - u) + 1 / d) * ∑' n : ℤ, ‖a' n‖ ^ 2) := by sorry
