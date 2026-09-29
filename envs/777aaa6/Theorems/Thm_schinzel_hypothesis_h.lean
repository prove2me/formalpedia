-- Prove2me | Theorems.Thm_schinzel_hypothesis_h
-- name    : schinzel_hypothesis_h
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:45:21.323683+00:00
-- url     : https://prove2.me/theorems/a5a37311-296d-48ee-8e22-3e0443423c62
-- statement:
--   Schinzel's Hypothesis H (1958): If f₁,...,fₖ are irreducible integer polynomials with positive leading coefficients and no prime divides ∏fᵢ(n) for all n, then all fᵢ are simultaneously prime for infinitely many n. Implies Bunyakovsky, twin primes, and Dirichlet's theorem.
-- source:
--   https://en.wikipedia.org/wiki/Schinzel%27s_hypothesis_H

import Mathlib

import Mathlib

theorem schinzel_hypothesis_h (k : ℕ) (hk : 1 ≤ k)
    (polys : Fin k → Polynomial ℤ)
    (hdeg : ∀ i, 1 ≤ (polys i).natDegree)
    (hlc : ∀ i, 0 < (polys i).leadingCoeff)
    (hirr : ∀ i, Irreducible (polys i))
    (hfix : ∀ p : ℕ, Nat.Prime p →
      ∃ n : ℤ, ∀ i, ¬(p : ℤ) ∣ (polys i).eval n) :
    {n : ℤ | ∀ i, Nat.Prime ((polys i).eval n).natAbs}.Infinite := by
  sorry
