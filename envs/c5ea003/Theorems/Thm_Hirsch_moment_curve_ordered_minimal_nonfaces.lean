-- Prove2me | Theorems.Thm_Hirsch_moment_curve_ordered_minimal_nonfaces
-- name    : Hirsch.moment_curve_ordered_minimal_nonfaces
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T03:08:12.865244+00:00
-- url     : https://prove2.me/theorems/07cdedd0-db22-48e8-897e-d9d3ab04bcf1
-- title:
--   Alternating moment labels form explicit minimal incompatible original-row families
-- statement:
--   For any injective real moment-parameter map a on m original labels, a half-dimension k and a map b selecting 2k+3 parameters in strictly increasing order, let N consist of the k+1 odd-ranked selected labels. In the original 2k-dimensional mean-centered moment inequality system (averaged over all m labels), prove that N has cardinality k+1, no feasible point makes all N rows tight, and every proper subset T of N has a feasible witness making exactly the rows in T tight. The barycentric signs, incompatibility, and proper-face feasibility are derived, not assumed. This assembles the ordered-sign and minimality bridge using the accepted small-face and barycentric proof bodies; it does not count the complete odd-label catalogue, assert a general diameter bound, or solve Polynomial Hirsch.
-- source:
--   Continuation of jjoshua2/prove2me-work #267/#281. Reuses exact namespace proof bodies from ACCEPTED #285 (small-face witness) and #286 (constructed barycentric nonfaces), with their root theorem/print suffixes excluded. New part derives ordered alternating signs, exact odd-set size and complete original-row minimality. Lagrange interpolation is classical and provided by Mathlib. No historical-priority claim.

import Mathlib

open scoped BigOperators

namespace Hirsch
theorem moment_curve_ordered_minimal_nonfaces (k m : ℕ) (a : Fin m → ℝ) (ha : Function.Injective a)
    (b : Fin (2 * k + 3) → Fin m) (hab : StrictMono (fun j => a (b j))) :
    let N : Finset (Fin m) := Finset.univ.image
      (fun j : Fin (k + 1) => b ⟨2 * j.val + 1, by have hj := j.isLt; omega⟩)
    let row : (Fin (2 * k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2 * k),
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j
    N.card = k + 1 ∧
    (¬ ∃ x : Fin (2 * k) → ℝ,
      (∀ i : Fin m, row x i ≤ 1) ∧ ∀ i ∈ N, row x i = 1) ∧
    ∀ T : Finset (Fin m), T ⊂ N →
      ∃ x : Fin (2 * k) → ℝ,
        (∀ i : Fin m, row x i ≤ 1) ∧
        ∀ i : Fin m, row x i = 1 ↔ i ∈ T := by sorry
end Hirsch
