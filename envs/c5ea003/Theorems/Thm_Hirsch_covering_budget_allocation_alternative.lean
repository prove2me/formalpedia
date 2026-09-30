-- Prove2me | Theorems.Thm_Hirsch_covering_budget_allocation_alternative
-- name    : Hirsch.covering_budget_allocation_alternative
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T23:49:43.657791+00:00
-- url     : https://prove2.me/theorems/124be5aa-74ac-45b3-be3b-f02f8f9d4242
-- title:
--   A full allocation alternative from finite covering resource budgets
-- statement:
--   Let a be a finite family of real continuous linear forms on R^k and B a second finite family of resource-budget forms. Suppose supplied nonnegative weights rho combine the B rows to a form whose value on each coordinate unit vector is at least one. For arbitrary original right sides b and arbitrary budget right sides t, a nonnegative vector satisfying a*x<=b and B*x<=t exists if and only if every nonnegative original/nonnegative/budget multiplier triple with zero combined row has nonnegative right-hand-side value. The returned dual system contains only actual rows, not an extra total-mass constraint. Budget rows may have signed coefficients, budgets may overlap, and budget right sides may be negative. Coverage is an explicit finite sufficient hypothesis; no Farkas or feasible-allocation oracle is assumed. The proof reduces to the accepted single-simplex alternative using a redundant global mass bound and absorbs its multiplier, including the nonnegativity correction needed when coverage is strict. No general unbounded-allocation, algorithm runtime, circuit-list coverage, or polytope-diameter theorem is claimed.
-- source:
--   Classical finite linear inequality alternative, supplied as a project-specific reduction from accepted PR #219, Hirsch.finite_allocation_minkowski_criterion (theorem 09c33216-ba2f-4c9f-b75e-e9d8279e8358), via its proved bounded-simplex allocation helper. Accepted source head 9d3aea2f4120f44a6c43b882d79c9f6f7fcb00c6; exact source blob 05926a8a263bde88f5d6bb29395d32f4ff97ccf8. No claim of a new classical Farkas theorem.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem covering_budget_allocation_alternative {m k r : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (b : Fin m → ℝ) (t : Fin r → ℝ) :
    (∃ x : Fin k → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, a i x ≤ b i) ∧ (∀ q, B q x ≤ t q)) ↔
    (∀ (w : Fin m → ℝ) (mu : Fin k → ℝ) (nu : Fin r → ℝ),
      (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ mu j) → (∀ q, 0 ≤ nu q) →
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
        (∑ q, nu q * B q (Pi.single j (1 : ℝ))) - mu j = 0) →
      0 ≤ (∑ i, w i * b i) + ∑ q, nu q * t q) := by sorry
end Hirsch
