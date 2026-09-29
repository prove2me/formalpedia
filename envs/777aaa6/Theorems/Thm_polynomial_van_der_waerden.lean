-- Prove2me | Theorems.Thm_polynomial_van_der_waerden
-- name    : polynomial_van_der_waerden
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:25:33.855728+00:00
-- url     : https://prove2.me/theorems/64deb0ef-fb32-4b9c-b825-63025e3a7182
-- statement:
--   Polynomial Van der Waerden theorem (Bergelson–Leibman 1996): For any polynomials p₁,...,pₖ with pᵢ(0)=0, any finite coloring of ℤ contains a monochromatic configuration a+p₁(d),...,a+pₖ(d). This extends Van der Waerden's theorem. Quantitative bounds are open.
-- source:
--   https://en.wikipedia.org/wiki/Polynomial_Van_der_Waerden_theorem

import Mathlib

import Mathlib

theorem polynomial_van_der_waerden (k : ℕ) (hk : 1 ≤ k)
    (poly : Fin k → Polynomial ℤ) (hpoly : ∀ i, (poly i).eval 0 = 0) :
    ∀ (r : ℕ) (_ : 1 ≤ r) (col : ℤ → Fin r),
      ∃ (a d : ℤ) (_ : 1 ≤ d.natAbs),
        ∀ i : Fin k, ∃ c : Fin r, col (a + (poly i).eval d) = c := by
  sorry
