-- Prove2me | Theorems.Thm_Hirsch_coverage_certificate_iff_no_recession
-- name    : Hirsch.coverage_certificate_iff_no_recession
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T00:32:09.5556+00:00
-- url     : https://prove2.me/theorems/cf116009-df29-405e-9304-46035751b50e
-- title:
--   Coverage certificates exactly exclude normalized resource-recession directions
-- statement:
--   For any finite family of real linear resource-budget rows B, a nonnegative combination of the rows dominates the all-ones mass functional coordinatewise if and only if there is no nonnegative vector v of total mass one with Bv<=0. For every explicitly nonempty nonnegative resource-feasible set {x>=0:Bx<=t}, existence of that same coverage certificate is equivalent to a finite upper bound on total mass. Signed row coefficients, arbitrary right sides, zero coordinates and empty row families are included. No Farkas, coverage-existence, recession-classification, strict-feasibility or full-rank premise is assumed. This characterizes coefficient-space boundedness, not boundedness of its image under a possibly noninjective generator map, and does not provide a graph-diameter bound.
-- source:
--   Classical finite-dimensional theorem of alternatives, derived here from accepted #219 bounded-simplex duality and #234 total-mass estimate. Helper proof bodies are reused verbatim from the accepted covering-budget artifact, solution SHA-256 0f3b70e88d6b989ccf2d3cc16676258ae714b6c05eefb49a9ba109a8729f7b3e. This is the coverage-condition completeness bridge for the project, not a historical novelty claim or a new Polynomial Hirsch theorem.

import Mathlib
open scoped BigOperators

namespace Hirsch
theorem coverage_certificate_iff_no_recession {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) :
    ((∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
        ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ↔
      ¬ ∃ v : Fin k → ℝ, (∀ j, 0 ≤ v j) ∧
        (∀ q, B q v ≤ 0) ∧ (∑ j, v j) = 1) ∧
    (∀ (t : Fin r → ℝ) (x : Fin k → ℝ),
      (∀ j, 0 ≤ x j) → (∀ q, B q x ≤ t q) →
      ((∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
          ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ↔
        ∃ R : ℝ, ∀ y : Fin k → ℝ, (∀ j, 0 ≤ y j) →
          (∀ q, B q y ≤ t q) → (∑ j, y j) ≤ R)) := by sorry
end Hirsch
