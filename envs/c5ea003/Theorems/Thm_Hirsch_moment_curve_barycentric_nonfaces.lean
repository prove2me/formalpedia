-- Prove2me | Theorems.Thm_Hirsch_moment_curve_barycentric_nonfaces
-- name    : Hirsch.moment_curve_barycentric_nonfaces
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T02:19:01.75119+00:00
-- url     : https://prove2.me/theorems/e37928aa-132f-4b32-ba91-47b4a1f75fa4
-- title:
--   Explicit barycentric weights certify both incompatible sign sides of original moment inequalities
-- statement:
--   For any finite injective real parameter family a on m labels, dimension d, and any selected label set s with at least d+2 members, construct the explicit inverse-product barycentric weights w_i=1/product_{j in s\{i}}(a_i-a_j). They are nonzero on s and annihilate every moment of degree at most d. For every point satisfying all ORIGINAL mean-centered moment inequalities in dimension d, there is a strictly slack selected row of negative weight and a strictly slack selected row of positive weight. Consequently neither weight-sign side can be simultaneously tight. No affine-dependence certificate, rank oracle, optimizer, feasibility witness or sign-partition assumption is supplied. The proof derives the weights identities from the leading coefficient of Lagrange interpolation and uses a nonzero slack polynomial. This formalizes the incompatibility mechanism complementary to accepted small-face witnesses #285; it does not formalize the odd-subset parity classification, minimal-nonface catalogue/cardinality, polytope realization or a Polynomial Hirsch bound.
-- source:
--   Direct polynomial/finite-sum proof using the pinned Mathlib Lagrange interpolation and polynomial root-uniqueness theorems. Complements jjoshua2/prove2me-work PR #285 and the geometric moment construction in research/STELLAR_NONFACE_PERSISTENCE.md (#267). Lagrange interpolation and moment-curve sign partitions are classical; no claim of historical novelty. The theorem does not import its own target or assume a moment-annihilation relation.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem moment_curve_barycentric_nonfaces (d m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (s : Finset (Fin m)) (hs : d + 2 ≤ s.card) :
    let w : Fin m → ℝ := fun i => (∏ j ∈ s.erase i, (a i - a j))⁻¹
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d,
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j
    (∀ i ∈ s, w i ≠ 0) ∧
    (∀ r : ℕ, r ≤ d → ∑ i ∈ s, w i * a i ^ r = 0) ∧
    ∀ x : Fin d → ℝ, (∀ i : Fin m, row x i ≤ 1) →
      (∃ i ∈ s, w i < 0 ∧ row x i < 1) ∧
      (∃ i ∈ s, 0 < w i ∧ row x i < 1) := by sorry
end Hirsch
