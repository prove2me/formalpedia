-- Prove2me | Theorems.Thm_Hirsch_moment_all_endpoint_monotone_routes
-- name    : Hirsch.moment_all_endpoint_monotone_routes
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-18T16:26:37.066214+00:00
-- url     : https://prove2.me/theorems/b6015256-7810-4aca-b2a0-136e13ee5e9c
-- title:
--   Target-monotone original-edge routes between all moment-polytope vertices
-- statement:
--   For every d<m and injective real node parameters a, form the original mean-centered moment inequalities row_i(x)<=1 in R^d. For ANY two actual extreme points u,v, define the score as the sum of v's tight original rows. Construct a finite natural-indexed route from u to v of length L<choose(m,d), consisting entirely of actual original extreme points. Every step strictly increases that fixed target score, and its entire closed segment is an exposed original edge; strict increase makes the edge nondegenerate. Every original target row already tight at a route point stays tight after the next step. No vertex catalogue, normalized directions, improving-pivot oracle, path or termination bound is supplied. The proof derives target displacement as a nonnegative combination of actual release directions, obtains a target-improving direction that cannot lose a shared target row, and assembles the full route by strict finite ascent using the accepted exact all-vertex catalogue. All dimensions including zero, odd dimensions, arbitrary real spacings, unsorted labels, negative-mean vertices and identical endpoints are retained. The bound can be exponential. This is not a polynomial diameter bound, a shortest or fully nonrevisiting path theorem, or a solution of unrestricted Polynomial Hirsch.
-- source:
--   New all-endpoint monotone assembly from accepted #298 moment_vertex_release_pivot (d86d447e-5259-4d8c-b963-6b8102e1e5be) and #299 moment_root_polynomial_vertex_catalogue (42f4500a-b696-4451-9d49-a13c7a2f98e5). Reuses the full accepted prefix through Hirsch.MomentRelease, plus the exact Hirsch.MomentRootCatalogue namespace from #299, removing only their old public root/axiom-print suffixes and deduplicating the byte-identical common prefix. At main539e0b0bd255682ff1115cf9d3e1c54b6822db2a. Classical feasible-cone/finite-ascent mathematics is credited; no historical novelty or improved general diameter claim. Distinct from #300's separated-pair polynomial route.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.moment_all_endpoint_monotone_routes (d m : ℕ) (hm : d < m) (a : Fin m → ℝ)
    (ha : Function.Injective a) (u v : Fin d → ℝ) :
    let row : (Fin d → ℝ) → Fin m → ℝ := fun x i =>
      ∑ j : Fin d, (a i ^ (j.val+1) - (∑ z, a z ^ (j.val+1)) / (m : ℝ)) * x j
    let P : Set (Fin d → ℝ) := {x | ∀ i, row x i ≤ 1}
    let J : Finset (Fin m) := Finset.univ.filter (fun i => row v i = 1)
    let score : (Fin d → ℝ) → ℝ := fun x => ∑ i ∈ J, row x i
    u ∈ P.extremePoints ℝ → v ∈ P.extremePoints ℝ →
      ∃ L : ℕ, L < Nat.choose m d ∧ ∃ p : ℕ → (Fin d → ℝ),
        p 0 = u ∧ p L = v ∧
        (∀ i, i ≤ L → p i ∈ P.extremePoints ℝ) ∧
        ∀ i, i < L → score (p i) < score (p (i+1)) ∧
          IsExposed ℝ P (segment ℝ (p i) (p (i+1))) ∧
          ∀ j, row (p i) j = 1 → row v j = 1 → row (p (i+1)) j = 1 := by sorry
