-- Prove2me | Theorems.Thm_Hirsch_moment_curve_compact_body
-- name    : Hirsch.moment_curve_compact_body
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T10:24:59.264888+00:00
-- url     : https://prove2.me/theorems/5f124c08-c2e5-4283-ada7-7c3ec7d0de86
-- title:
--   Original mean-centered moment inequalities form a compact convex body with explicit coordinate bounds
-- statement:
--   For any positive half-dimension k, more than 2k distinct real moment parameters on m original labels define their mean-centered dimension-2k inequality set P by all original rows <=1. Prove P compact and convex, with zero in its ordinary ambient interior. For each original row construct a feasible point making it equal to one and every other row strictly less than one. Derive an explicit coordinate box from m times the sums of absolute coefficients of the Lagrange nodal basis. No boundedness, full-rank inverse, vertex catalogue, compactness, feasible support point, or polytope realization is supplied as a premise. The result supplies original-space compact/full-dimensional realization facts; it does not formalize simplicity, a complete facet-lattice identification, asymptotics, or a uniform diameter bound.
-- source:
--   Continuation of accepted #285/#286/#288 and the distinct realization gap beyond #289. The SmallFaces and MomentBarycentric namespace proof bodies are reused from accepted #288 (blobe85d05dd4a6208ff8311809d1f456d9c6a84d011); one unused membership binder is named hi instead of underscore, otherwise the dependency bodies are unchanged; earlier public targets are not resubmitted. New boundedness follows from nonnegative slack values with total m and Mathlib Lagrange interpolation. Closedness/compact box, convexity and ambient interior are proved directly. Classical moment-curve geometry and interpolation are not claimed as historically novel.

import Mathlib

open scoped BigOperators

namespace Hirsch
theorem moment_curve_compact_body (k m : ℕ) (hk : 0 < k) (hm : 2 * k < m)
    (a : Fin m → ℝ) (ha : Function.Injective a) :
    let row : (Fin (2 * k) → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin (2 * k),
        (a i ^ (j.val + 1) - (∑ l, a l ^ (j.val + 1)) / (m : ℝ)) * x j
    let P : Set (Fin (2 * k) → ℝ) := {x | ∀ i : Fin m, row x i ≤ 1}
    IsCompact P ∧ Convex ℝ P ∧ (0 : Fin (2 * k) → ℝ) ∈ interior P ∧
    (∀ i : Fin m, ∃ x : Fin (2 * k) → ℝ,
      x ∈ P ∧ row x i = 1 ∧ ∀ l : Fin m, l ≠ i → row x l < 1) ∧
    ∀ x ∈ P, ∀ j : Fin (2 * k),
      |x j| ≤ (m : ℝ) * ∑ i : Fin m,
        |(Lagrange.basis Finset.univ a i).coeff (j.val + 1)| := by sorry
end Hirsch
