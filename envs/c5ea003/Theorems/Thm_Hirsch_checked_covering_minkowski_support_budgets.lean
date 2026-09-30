-- Prove2me | Theorems.Thm_Hirsch_checked_covering_minkowski_support_budgets
-- name    : Hirsch.checked_covering_minkowski_support_budgets
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T00:26:32.226992+00:00
-- url     : https://prove2.me/theorems/44ee8d0b-dcc7-4b12-aae2-92aff22ab5da
-- title:
--   Actual checked circuit output gives exact Minkowski support budgets for covering allocation systems
-- statement:
--   For finite original real continuous-linear inequalities, a finite generator map, and separately or jointly constrained allocation budgets, assume finite nonnegative budget-row coverage, exact rational correspondence of all original/nonnegative/budget allocation rows via a supplied bijection, a passing executable rational circuit-catalogue audit, finite budget-row domination certificates for candidate support, and exact original-H primal/dual support witnesses for each emitted circuit. Whole-set Minkowski reconstruction by the derived erosion and allocated candidate is equivalent to the explicit scalar inequalities of the actual emitted catalogue. The pointwise feasibility criterion and sufficiency are derived from accepted proofs, not assumed. All objective correspondence and candidate-support certificates are finite coordinate identities/inequalities; the witnesses are supplied rather than discovered. The original H-polyhedron need not be bounded or full-dimensional, generators may be dependent, and budgets can overlap or have signed entries/RHS when the explicit coverage and support hypotheses hold. No semantic catalogue completeness, Farkas, or diameter premise is assumed. This is one complete formal certificate-composition result, not a polynomial graph-diameter theorem or an unconditional shape-selection algorithm.
-- source:
--   Direct composition of accepted #233 checked catalogue dual tests, accepted #234 covering allocation alternative, and exact support-certificate algebra as in #227. Helper bodies reused verbatim from downloaded verified artifacts. No new classical duality claim.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem checked_covering_minkowski_support_budgets
    (d m k r n : ℕ) (e : (Fin m ⊕ (Fin k ⊕ Fin r)) ≃ Fin n)
    (a : Fin m → (Fin d → ℝ) →L[ℝ] ℝ)
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ))
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (M : Fin k → Fin n → ℚ) (tag : Finset (Fin n) → Bool)
    (L : Finset (Fin n) → Fin n → Option (Fin k) → ℚ)
    (z : Finset (Fin n) → Fin n → ℚ)
    (ha : ∀ i j, (M j (e (.inl i)) : ℝ) = -a i (G (Pi.single j (1 : ℝ))))
    (hneg : ∀ i j, (M j (e (.inr (.inl i))) : ℝ) = if i = j then -1 else 0)
    (hB : ∀ q j, (M j (e (.inr (.inr q))) : ℝ) = B q (Pi.single j (1 : ℝ)))
    (b h : Fin m → ℝ) (t : Fin r → ℝ)
    (eta : Fin m → Fin r → ℝ) (heta : ∀ i q, 0 ≤ eta i q)
    (hdom : ∀ i j, a i (G (Pi.single j (1 : ℝ))) ≤
      ∑ q, eta i q * B q (Pi.single j (1 : ℝ)))
    (hcap : ∀ i, (∑ q, eta i q * t q) ≤ h i)
    (alpha : (Fin n → ℚ) → Fin m → ℝ) (xstar : (Fin n → ℚ) → Fin d → ℝ) :
    let U := (Finset.range (k + 2)).biUnion
      (fun s => (Finset.univ : Finset (Fin n)).powersetCard s)
    let v : Finset (Fin n) → Fin n → ℚ := fun s i => if i ∈ s then L s i none else 0
    let C := (U.filter (fun s => tag s = false ∧ (∀ i ∈ s, 0 < L s i none) ∧
      (∀ j, (∑ i, M j i * v s i) = 0) ∧ (∑ i, v s i) = 1)).image v
    decide (∀ s ∈ U, if tag s then
        (∃ i, z s i ≠ 0) ∧ (∀ i, i ∉ s → z s i = 0) ∧
          (∀ j, (∑ i, M j i * z s i) = 0) ∧ (∑ i, z s i) = 0
      else ∀ i ∈ s, ∀ j ∈ s,
        (∑ q, L s i (some q) * M q j) + L s i none = if i = j then 1 else 0) = true →
    (∀ c ∈ C, ∀ i, 0 ≤ alpha c i) →
    (∀ c ∈ C, ∀ i, a i (xstar c) ≤ b i) →
    (∀ c ∈ C, ∀ j,
      (∑ i, (c (e (.inl i)) : ℝ) * a i (Pi.single j (1 : ℝ))) =
        ∑ i, alpha c i * a i (Pi.single j (1 : ℝ))) →
    (∀ c ∈ C, ∀ i, alpha c i * (b i - a i (xstar c)) = 0) →
    (({x : Fin d → ℝ | ∀ i, a i x ≤ b i} =
      {x : Fin d → ℝ | ∃ p : Fin d → ℝ, (∀ i, a i p ≤ b i - h i) ∧
        ∃ θ : Fin k → ℝ, (∀ j, 0 ≤ θ j) ∧ (∀ q, B q θ ≤ t q) ∧ p + G θ = x}) ↔
    ∀ c ∈ C,
      (∑ i, (c (e (.inl i)) : ℝ) * h i) -
        (∑ q, (c (e (.inr (.inr q))) : ℝ) * t q) ≤
          (∑ i, (c (e (.inl i)) : ℝ) * b i) - ∑ i, alpha c i * b i) := by sorry
end Hirsch
